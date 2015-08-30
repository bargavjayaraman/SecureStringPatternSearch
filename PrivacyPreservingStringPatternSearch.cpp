#include "polarssl/aes.h"
#include "polarssl/entropy.h"
#include "polarssl/ctr_drbg.h"
#include "polarssl/config.h"
#include "polarssl/sha1.h"
#include<algorithm>
#include<map>
#include<set>
#include<queue>
#include<vector>
#include<tr1/unordered_map>
#include<tr1/unordered_set>
#include<fstream>
#include<ctype.h>
#include<string.h>
#include<dirent.h>
#include<time.h>
#include<math.h>
#include<stdlib.h>

/*
	m/n = 6, k = 5 (8 hash keys)
	m/n = 8, k = 6 (10 hash keys)
	m/n = 10, k = 7 (12 hash keys)
	m/n = 12, k = 8 (14 hash keys)
*/

#define NUM_KWS   1000
#define NUM_FILES (NUM_KWS/10)
#define MbyN	  10
#define K	  7
#define S_SIZE	  44
#define P	  33073

using namespace std;
using namespace tr1;

struct pairs
{
	string id;
	float val;
};

struct Qobj
{
	string name;
	float val;	
};

class Qcomp
{
	public:
	bool operator() (Qobj a, Qobj b)
	{
		return a.val > b.val;
	}
};

typedef priority_queue<Qobj, vector<Qobj>, Qcomp> PQ;

struct a_list
{
	vector<pairs> docIDs;
	int wordDepth;
	unordered_map<string, int> a_words;
};

unsigned char key[32];

unsigned char hashKey[7][20];
unsigned char iv[16], iv_save[16];
unsigned char ip[128], op[128];
aes_context aes;

unsigned int subs, pres, coeffs, numdocs;
fstream out;
unordered_set<string> stopwords;
map<string, a_list> inverted_table;
map<int, map<int, vector<string> > > resultset;
set<string> chosenDocs, chosenFpWords, allKeywords;
vector<string> keywords, fpWords;
vector<int> primes;
unordered_map<string, unordered_set<string> > substrings;

int counter[25];
set<string> allsubs, allpres;
unordered_map<string, unordered_map<string, float> > sims;
unordered_map<string, vector<pairs> > inverted_table2;
unordered_set<string> init_table;
struct R
{
	float acc;
	int cnt;
};
map<int, R> ranking;

struct splitnode
{
	vector<string> kws;
	splitnode *left;
	splitnode *right;
}*splitroot;

struct DocID
{
	string fileID;
	unsigned int nextKey;
};

struct Poly
{
	vector<DocID> doclist;
	unsigned int *coeff, Kinit, Z;
	int degree;
};

struct bloomnode
{
	int *bloom;
	int *prefixBloom;
	int bloomsize;
	int prefixBloomsize;
	Poly *poly;
	unsigned int bloomID, prefixBloomID;
	bloomnode *left;
	bloomnode *right;
}*bloomroot;

void 	check(char *);
bool 	check_stopword(char *);
float  	getWeight(string, string);
void    storeInBloom(int *, int, unsigned int, string);
void    storeInPrefixBloom(int *, int, unsigned int, string, unsigned int);

unsigned int murmur( const void * key, int len, unsigned int seed , int range)
{
	const unsigned int m = 0x5bd1e995;
	const int r = 24;
	unsigned int h = seed ^ len;
	const unsigned char * data = (const unsigned char *)key;
	while(len >= 4)
	{
		unsigned int k = *(unsigned int *)data;
		k *= m;
		k ^= k >> r;
		k *= m;

		h *= m;
		h ^= k;

		data += 4;
		len -= 4;
	}
	switch(len)
	{
	case 3: h ^= data[2] << 16;
	case 2: h ^= data[1] << 8;
	case 1: h ^= data[0];
		h *= m;
	};
	h ^= h >> 13;
	h *= m;
	h ^= h >> 15;
	return (unsigned int)h%range;
}

bool mysort(pairs it1, pairs it2)
{
	return it1.val > it2.val;
}

void getPrimes()
{
	ifstream fin;
	int num;
	fin.open("primes.txt", ios::in);
	while(fin>>num)
		primes.push_back(num);
	fin.close();
}

void getFpWords()
{
	ifstream fin;
	char word[65];
	fin.open("primes.txt", ios::in);
	while(fin>>word)
		fpWords.push_back(word);
	fin.close();
}

void getStopwords()
{
	ifstream fin;
	char word[25];
	fin.open("stop-words-1.txt", ios::in);
	while(fin>>word)
		stopwords.insert(word);
	fin.close();
}

bool isLess(string a, string b)
{
	for(int i = 0; a[i] != '\0' || b[i] != '\0'; i++)
	{
		if(a[i] < b[i])
			return true;
		else if(a[i] > b[i])
			return false;
	}
	return true;
}

void getKeywords(char *file)
{
	ifstream f;
	char s[3000];
	char str[60], a[60];
	strcpy(a, "we//");
	strcat(a, file);
	f.open(a, ios::in);
	while(!f.eof())
	{
		f>>s;
		strncpy(str, s, 59);
		str[59] = '\0';
		check(str);
		if(check_stopword(str))
			continue;
		if(strlen(str) > 10)
			continue;
		init_table.insert(str);
	}
	f.close();
}

void readfile(char *file)
{
	ifstream f;
	char s[3000];
	char str[60], a[60], b[12];
	bool flag = false;
	strcpy(a, "we//");
	strcat(a, file);
	f.open(a, ios::in);
	while(!f.eof())
	{
		f>>s;
		strncpy(str, s, 59);
		str[59] = '\0';
		check(str);
		if(check_stopword(str))
			continue;
		if(allKeywords.find(str) == allKeywords.end())
			continue;
		if((inverted_table[str].docIDs.size() == 0) || (inverted_table[str].docIDs.back().id != file))
		{
			pairs tmp = {file, 1};
			inverted_table[str].docIDs.push_back(tmp);
		}
		else
			inverted_table[str].docIDs.back().val += 1;
		if(!flag)
		{
			strcpy(b, str);
			flag = true;
		}
		else
		{
			inverted_table[b].a_words[str] += 1;
			strcpy(b, str);
		}
	}
	f.close();
}

void check(char *str)
{
	int i,j;
	for(i=0;str[i]!='\0';i++)
	{
		if(!isalpha(str[i]))
		{
			for(j=i;str[j]!='\0';j++)
				str[j]=str[j+1];
			str[j]='\0';
			i--;
		}
		else
			str[i]=tolower(str[i]);
	}
}

bool check_stopword(char *str)
{
	return (stopwords.find(str) != stopwords.end()) || (strlen(str) <= 2);
}

void createSplitRoot()
{
	splitroot = new splitnode;
	for(map<string, a_list >::iterator it = inverted_table.begin(); it != inverted_table.end(); it++)
	{
		splitroot->kws.push_back((*it).first);
		numdocs += (*it).second.docIDs.size();
	}
	splitroot->left = splitroot->right = NULL;
}

void PAM(vector<string> S, int s, string *m1, string *m2)
{
	int r1, r2;
	float sim[s][s], cost = 0, new_cost1, new_cost2;
	int cand[s];
	
	for(int i = 0; i < s; i++)
	{
		for(int j = i + 1; j < s; j++)
		{
			if(sims[S[i]].find(S[j]) == sims[S[i]].end())
				sims[S[j]][S[i]] = sims[S[i]][S[j]] = getWeight(S[i], S[j]);
			sim[i][j] = sim[j][i] = sims[S[i]][S[j]];
		}
	}
	r1 = rand()%s;
	while( (r2 = rand()%s) == r1);
	for(int i = 0; i < s; i++)
	{
		cand[i] = i;
		if(i == r1 || i == r2)
			cand[i] = -1;
	}
	for(int i = 0; i < s; i++)
	{
		if(i == r1 || i == r2)
			continue;
		cost += (sim[r1][i] > sim[r2][i]) ? sim[r1][i] : sim[r2][i];
	}
	for(int it = 0; it < s; it++)
	{
		if(cand[it] == -1)
			continue;
		new_cost1 = new_cost2 = 0;
		for(int i = 0; i < s; i++)
		{
			if(i == cand[it] || i == r2)
				continue;
			new_cost1 += (sim[cand[it]][i] > sim[r2][i]) ? sim[cand[it]][i] : sim[r2][i];
		}
		for(int i = 0; i < s; i++)
		{
			if(i == cand[it] || i == r1)
				continue;
			new_cost2 += (sim[cand[it]][i] > sim[r1][i]) ? sim[cand[it]][i] : sim[r1][i];
		}
		if(new_cost1 > new_cost2)
		{
			if(new_cost1 > cost)
			{
				cost = new_cost1;
				r1 = cand[it];
			}
		}
		else
		{
			if(new_cost2 > cost)
			{
				cost = new_cost2;
				r2 = cand[it];
			}
		}
	}
	*m1 = S[r1];
	*m2 = S[r2];
}

float getMedoid(splitnode *node, string *m1, string *m2)
{
	int r;
	float a, b, cost = 0;
	unordered_set<int> used;
	vector<string> S;
	while(S.size() != S_SIZE)
	{
		r = rand()%node->kws.size();
		if(used.find(r) == used.end())
		{
			S.push_back(node->kws[r]);
			used.insert(r);
		}
	}
	PAM(S, S_SIZE, m1, m2);
	for(vector<string>::iterator it = node->kws.begin(); it != node->kws.end(); it++)
	{
		if(*it != *m1 && *it != *m2)
		{
			if(sims[*it].find(*m1) == sims[*it].end())
				sims[*m1][*it] = sims[*it][*m1] = getWeight(*it, *m1);
			a = sims[*it][*m1];
			if(sims[*it].find(*m2) == sims[*it].end())
				sims[*m2][*it] = sims[*it][*m2] = getWeight(*it, *m2);
			b = sims[*it][*m2];
			cost += (a > b) ? a : b;
		}
	}
	return cost;
}

void createSplitTree(splitnode *node)
{
	vector<string> L, R, S, dummy;
	int k = 0, c, num;
	float cost1, cost2, a, b;
	PQ Q;
	bool flag = false;
	splitnode *leftNode, *rightNode;
	string *m1, *m2, *m3, *m4, *m5, *m6, *m7, *m8, *m9, *m10, *o1, *o2;
	m1 = new string();m2 = new string();o1 = new string();o2 = new string();	

	if(node->kws.size() <= 1)
		return;
	if(node->kws.size() <= S_SIZE)
		PAM(node->kws, node->kws.size(), o1, o2);
	// get random S_SIZE kws and form a vector S, send it to PAM
	else if(node->kws.size() <= S_SIZE*3)
	{
		cost1 = getMedoid(node, o1, o2);
	}
	else if(node->kws.size() <= S_SIZE*5)
	{
		// call 2 times
		cost1 = getMedoid(node, o1, o2);
		cost2 = getMedoid(node, m1, m2);
		if(cost2 > cost1)
		{
			*o1 = *m1; *o2= *m2;
		}
	}
	else
	{
		// call 5 times
		cost1 = getMedoid(node, o1, o2);
		for(int run = 1; run < 5; run++)
		{
			cost2 = getMedoid(node, m1, m2);
			if(cost2 > cost1)
			{
				*o1 = *m1; *o2= *m2;
				cost1 = cost2;
			}
		}
		// get max cost as medoids..
	}
	L.push_back(*o1);
	R.push_back(*o2);
	for(vector<string>::iterator it = node->kws.begin(); it != node->kws.end(); it++)
	{
		if(*it == *o1 || *it == *o2)
			continue;
		if(sims[*it].find(*o1) == sims[*it].end())
			sims[*o1][*it] = sims[*it][*o1] = getWeight(*it, *o1);
		a = sims[*it][*o1];
		if(sims[*it].find(*o2) == sims[*it].end())
			sims[*o2][*it] = sims[*it][*o2] = getWeight(*it, *o2);
		b = sims[*it][*o2];
		if(a > b)
			L.push_back(*it);
		else
			R.push_back(*it);
	}
	// make clusters
	if(L.size() < R.size())
	{
		dummy = L;
		L = R;
		R = dummy;
		flag = true;
	}
	num = (L.size()-R.size())/2;
	for(vector<string>::iterator it = L.begin(); it != L.end(); it++)
	{
		if(num == 0)
			break;
		if(k++ < num)
		{
			Qobj ob;
			ob.name = *it;
			ob.val = sims[*it][*R.begin()];
			Q.push(ob);
		}
		else
		{
			Qobj ob;
			ob.name = *it;
			ob.val = sims[*it][*R.begin()];
			if(ob.val > Q.top().val)
			{
				Q.pop();
				Q.push(ob);
			}
		}
	}
	while(!Q.empty())
	{
		L.erase(find(L.begin(), L.end(), Q.top().name));
		R.push_back(Q.top().name);
		Q.pop();
	}
	if(flag)
	{
		dummy = L;
		L = R;
		R = dummy;
	}
	leftNode = new splitnode;
	leftNode->kws = L;
	leftNode->left = leftNode->right = NULL;

	rightNode = new splitnode;
	rightNode->kws = R;
	rightNode->left = rightNode->right = NULL;

	node->left = leftNode;
	node->right = rightNode;
	delete(m1);delete(m2);delete(o1);delete(o2);
	createSplitTree(leftNode);
	createSplitTree(rightNode);
}

float getWeight(string a, string b)
{
	int wt1 = 0, wt2 = 0, wt3 = 0, tot1 = 0, tot2 = 0;

	if(substrings[a].size() >= substrings[b].size())
	{
		for(unordered_set<string>::iterator it = substrings[b].begin(); it != substrings[b].end(); it++)
			if(substrings[a].find(*it) != substrings[a].end())
				wt1++;
	}
	else
	{
		for(unordered_set<string>::iterator it = substrings[a].begin(); it != substrings[a].end(); it++)
			if(substrings[b].find(*it) != substrings[b].end())
				wt1++;
	}
	tot1 = substrings[a].size() + substrings[b].size() - wt1;
	vector<pairs>:: iterator it1 = inverted_table[a].docIDs.begin();
	vector<pairs>:: iterator it2 = inverted_table[b].docIDs.begin();
	while(it1 != inverted_table[a].docIDs.end() && it2 != inverted_table[b].docIDs.end())
	{
		if((*it1).id == (*it2).id)
		{
			wt2++;
			it1++;
			it2++;
		}
		else if(isLess((*it1).id, (*it2).id))					
			it1++;
		else
			it2++;
	}
	tot2 = inverted_table[a].docIDs.size() + inverted_table[b].docIDs.size() - wt2;
	if(inverted_table[a].a_words.find(b) != inverted_table[a].a_words.end())
		wt3 += inverted_table[a].a_words[b];
	if(inverted_table[b].a_words.find(a) != inverted_table[b].a_words.end())
		wt3 += inverted_table[b].a_words[a];
	if(wt3 > wt2)
		wt3 = wt2;
	return (float)wt1/tot1 + (float)wt2/tot2 + (float)wt3/tot2;
}

int getNearestPrime(int num)
{
	int low = 0, high = primes.size() - 1, mid;
	while(low <= high)
	{
		mid = (low + high)/2;
		if(primes[mid] < num)
			low = mid + 1;
		else
			high = mid - 1;
	}
	return (primes[mid] <= num)?primes[mid]:primes[mid-1];
}

void createBloomTree(bloomnode *bnode, splitnode *snode, int currentDepth)
{
	bloomnode *lbnode, *rbnode;
	unsigned int val, numbitsbf, numbitspbf, numintsbf, numintspbf, bfsize = 0, pbfsize = 0, *roots, key;
	char str[129], buffer[33];

	for(vector<string>::iterator it = snode->kws.begin(); it != snode->kws.end(); it++)
	{
		pbfsize += (*it).length() - 1;
		bfsize += ((*it).length() * ((*it).length()-1)) / 2;
	}
	if(bnode == bloomroot)
	{
		subs = bfsize;
		pres = pbfsize;
	}
	if(!snode->left && !snode->right)
	{
		bfsize = 45;
		pbfsize = 9;
		numbitsbf = bfsize*12;
		numbitspbf = pbfsize*12;
	}
	else
	{
		numbitsbf = bfsize*MbyN;
		numbitspbf = pbfsize*MbyN;
	}
	bnode->left = bnode->right = NULL;
	numintsbf = ceil(numbitsbf/32.0);
	bnode->bloom = new int[numintsbf];
	memset(bnode->bloom, 0, numintsbf*4);
	
	numintspbf = ceil(numbitspbf/32.0);
	bnode->prefixBloom = new int[numintspbf];
	memset(bnode->prefixBloom, 0, numintspbf*4);
	bnode->bloomID = rand();
	bnode->prefixBloomID = rand();
	
	bnode->bloomsize = getNearestPrime(numbitsbf);
	bnode->prefixBloomsize = getNearestPrime(numbitspbf);
	if(snode->left)
	{
		lbnode = new bloomnode;
		bnode->left = lbnode;
		createBloomTree(lbnode, snode->left, currentDepth+1);
	}
	if(snode->right)
	{
		rbnode = new bloomnode;
		bnode->right = rbnode;
		createBloomTree(rbnode, snode->right, currentDepth+1);
	}
	if(snode->kws.size() == 1)
	{
		bnode->poly = new Poly;
		bnode->poly->Z = rand();
		bnode->poly->Kinit = rand()%P;
		string word = *snode->kws.begin();
		int l = 0, r, i, t = substrings[word].size();
		if(t == 45)
			r = 0;
		else if(t >= 30)
			r = rand()%(45-t);
		else if(t < 30)
			r = (rand()%15) + 30-t;
		bnode->poly->degree = r + t + 1;		
		roots = new unsigned int[bnode->poly->degree-1];
		bnode->poly->coeff = new unsigned int[bnode->poly->degree];
		coeffs += bnode->poly->degree;
		for(unordered_set<string>::iterator it = substrings[word].begin(); it != substrings[word].end(); it++)
			roots[l++] = murmur((*it).c_str(), (*it).length(), bnode->poly->Z, P);
		while(l < bnode->poly->degree-1)
			roots[l++] = rand()%P;
		bnode->poly->coeff[0] = (P-roots[0])%P;
		bnode->poly->coeff[1] = 1;
		for(i = 2; i < bnode->poly->degree; i++)
		{
			bnode->poly->coeff[i] = 0;
			for(int j = i; j > 0; j--)
				bnode->poly->coeff[j] = ( (bnode->poly->coeff[j] * ((P-roots[i-1])%P)%P) + bnode->poly->coeff[j-1] )%P;
			bnode->poly->coeff[0] = (bnode->poly->coeff[0]*((P-roots[i-1])%P))%P;
		}
		bnode->poly->coeff[0] = (bnode->poly->coeff[0] + bnode->poly->Kinit)%P;
		inverted_table[word].wordDepth = currentDepth;
		storeInBloom(bnode->bloom, bnode->bloomsize, bnode->bloomID, word);
		storeInPrefixBloom(bnode->prefixBloom, bnode->prefixBloomsize, bnode->prefixBloomID, word, 0);
		key = bnode->poly->Kinit;
		while(inverted_table[word].docIDs.size())
		{
			DocID *doc = new DocID;
			snprintf(buffer, sizeof(buffer), "%u", key);
			doc->fileID = (*inverted_table[word].docIDs.begin()).id;
			for(i = 0; i < strlen(buffer); i++)
				doc->fileID[i] ^= buffer[i];
			doc->nextKey = (rand()%P) ^ key;
			key ^=	doc->nextKey;
			bnode->poly->doclist.push_back(*doc);
			inverted_table[word].docIDs.erase(inverted_table[word].docIDs.begin());
		}
		delete(roots);
	}
	else
	{
		for(vector<string>::iterator it = snode->kws.begin(); it != snode->kws.end(); it++)
		{
			storeInBloom(bnode->bloom, bnode->bloomsize, bnode->bloomID, *it);
			storeInPrefixBloom(bnode->prefixBloom, bnode->prefixBloomsize, bnode->prefixBloomID, *it, inverted_table[*it].wordDepth-currentDepth);
		}
	}

	for(int i = 0; i < K*(bfsize-allsubs.size()); i++)
	{
		val = rand()%numbitsbf;
		bnode->bloom[val/32] |= 1<<(val%32);
	}

	for(int i = 0; i < K*(pbfsize-allpres.size()); i++)
	{
		val = rand()%numbitspbf;
		bnode->prefixBloom[val/32] |= 1<<(val%32);
	}
	allsubs.clear();
	allpres.clear();
	delete(snode);
}

void storeInBloom(int *bloom, int bloomsize, unsigned int bloomID, string word)
{
	unsigned int v[7], i, run, hashVal;
	char str[200], buffer[33];
	unsigned char hashStr[20], hashFinal[20];
	
	allsubs.insert(substrings[word].begin(), substrings[word].end());
	
	for(unordered_set<string>::iterator it = substrings[word].begin(); it != substrings[word].end(); it++)
	{	
		strcpy(str, (*it).c_str());
		snprintf(buffer, sizeof(buffer), "%d", bloomID);	
		for(run = 0; run < 7; run++)
		{
			sha1_hmac(hashKey[run], 20, (unsigned char*)str, strlen(str), hashStr);
			sha1_hmac(hashStr, 20, (unsigned char*)buffer, strlen(buffer), hashFinal);
			hashVal = 0;
			for(i = 0; i < 20; i++)
				hashVal ^= hashFinal[i]<<(8*(i%4));
			v[run] = hashVal%bloomsize;
			bloom[v[run]/32] |= 1<<(v[run]%32);
		}		
	}
}

void storeInPrefixBloom(int *bloom, int bloomsize, unsigned int bloomID, string word, unsigned int startPoint)
{
	unsigned int v[7], i, j, k, run, hashVal;
	char str[200], buffer[33];
	unsigned char hashStr[20], hashFinal[20];
	
	if(startPoint < word.length()-1)
	{
		for(j = startPoint+2; j < word.length()+1; j++)
		{
			allpres.insert(word.substr(startPoint, j-startPoint));
			strcpy((char *)ip, word.substr(startPoint, j-startPoint).c_str());
			for(k = strlen((char *)ip); k < 128; k++)
				ip[k] = '0';
			for(k = 0; k < 16; k++)
				iv[k] = iv_save[k];
			aes_crypt_cbc( &aes, AES_ENCRYPT, 16, iv, ip, op );
			for(k = 0; k < 128; k++)
			{
				str[k] = op[k];
				if(str[k] == '\0')
					str[k] = '0';
			}
			str[128] = '\0';
			snprintf(buffer, sizeof(buffer), "%d", bloomID);
			for(run = 0; run < 7; run++)
			{
				sha1_hmac(hashKey[run], 20, (unsigned char*)str, strlen(str), hashStr);
				sha1_hmac(hashStr, 20, (unsigned char*)buffer, strlen(buffer), hashFinal);
				hashVal = 0;
				for(i = 0; i < 20; i++)
					hashVal ^= hashFinal[i]<<(8*(i%4));
				v[run] = hashVal%bloomsize;
				bloom[v[run]/32] |= 1<<(v[run]%32);
			}
		}
	}
}

bool searchInBloom(int *bloom, int bloomsize, unsigned int bloomID, char *str)
{
	unsigned int v[7], run, i, hashVal, ret = 1;
	char buffer[33];
	unsigned char hashStr[20], hashFinal[20];

	snprintf(buffer, sizeof(buffer), "%d", bloomID);
	for(run = 0; run < 7; run++)
	{
		sha1_hmac(hashKey[run], 20, (unsigned char*)str, strlen(str), hashStr);
		sha1_hmac(hashStr, 20, (unsigned char*)buffer, strlen(buffer), hashFinal);
		hashVal = 0;
		for(i = 0; i < 20; i++)
			hashVal ^= hashFinal[i]<<(8*(i%4));
		v[run] = hashVal%bloomsize;
		ret = ret && (bloom[v[run]/32] & 1<<(v[run]%32));
	}
	return ret;
}

unsigned int evaluatePoly(Poly *poly, char *str)
{
	unsigned int val = 0, x;
	x = murmur(str, strlen(str), poly->Z, P);
	for(int i = poly->degree-1; i >= 0; i--)
	{
		val = (val * x)%P;
		val = (val + poly->coeff[i])%P;
	}
	return val;
}

void search(bloomnode *curr, char *searchString, int depth, int currRank)
{
	char buffer[33], file[33];
	unsigned int key;
	int i;
	if(!curr || !searchInBloom(curr->bloom, curr->bloomsize, curr->bloomID, searchString))
		return;
	if(searchInBloom(curr->prefixBloom, curr->prefixBloomsize, curr->prefixBloomID, searchString))
		currRank = depth;
	search(curr->left, searchString, depth+1, currRank);
	search(curr->right, searchString, depth+1, currRank);
	if(!curr->left && !curr->right)
	{
		if(currRank != 99)
		{
			if(evaluatePoly(curr->poly, searchString) == curr->poly->Kinit)
			{
				key = curr->poly->Kinit;
				for(vector<DocID>::iterator it = curr->poly->doclist.begin(); it != curr->poly->doclist.end(); it++)
				{
					snprintf(buffer, sizeof(buffer), "%u", key);
					for(i = 0; i < strlen(buffer); i++)
						file[i] = (*it).fileID[i] ^ buffer[i];
					while((*it).fileID[i] != '\0')
					{
						file[i] = (*it).fileID[i];
						i++;
					}
					file[i] = '\0';
					key ^= (*it).nextKey;
					resultset[depth - currRank][counter[depth - currRank]].push_back(file);
				}
				counter[depth - currRank] += 1;
			}
		}
		else
			resultset[99][0].push_back("False");
	}
}

void searchOnQueryRel(string q, bool type)
{
	char word[129];
	int i, found;
	map<int, unordered_set<string> > actualRanking, finalRanking;
	map<int, map<int, vector<string> > > abc;

	strcpy((char *)ip, q.c_str());
	for(i = strlen((char *)ip); i < 128; i++)
		ip[i] = '0';
	for(i = 0; i < 16; i++)
		iv[i] = iv_save[i];
	aes_crypt_cbc( &aes, AES_ENCRYPT, 16, iv, ip, op );
	for(i = 0; i < 128; i++)
	{
		word[i] = op[i];
		if(word[i] == '\0')
			word[i] = '0';
	}
	word[128] = '\0';
	for(i = 0; i < 25; i++)
		counter[i] = 0;
	search(bloomroot, word, 1, 99);
	i = 1;
	for(map<int, map<int, vector<string> > >::iterator it1 = resultset.begin(); it1 != resultset.end(); it1++)
	{
		if((*it1).first == 99)
			continue;
		while(true)
		{
			for(map<int, vector<string> >::iterator it2 = (*it1).second.begin(); it2 != (*it1).second.end(); it2++)
			{
				if((*it2).second.size())
				{
					finalRanking[i].insert(*(*it2).second.begin());
					(*it2).second.erase((*it2).second.begin());
				}
			}
			if(finalRanking[i].empty())
			{
				finalRanking.erase(i);
				break;
			}
			i++;
		}
		if(!type)
			break;			
	}
	resultset.clear();
	
	for(i = 0; i < 25; i++)
		counter[i] = 0;
	for(unordered_map<string, vector<pairs> >::iterator it1 = inverted_table2.begin(); it1 != inverted_table2.end(); it1++)
	{
		if((*it1).first.find(q) != string::npos)
		{
			i = (*it1).first.find(q);
			for(vector<pairs>::iterator it2 = (*it1).second.begin(); it2 != (*it1).second.end(); it2++)
				abc[i][counter[i]].push_back((*it2).id);
			counter[i] += 1;
		}
	}
	i = 1;
	for(map<int, map<int, vector<string> > >::iterator it1 = abc.begin(); it1 != abc.end(); it1++)
	{
		while(true)
		{
			for(map<int, vector<string> >::iterator it2 = (*it1).second.begin(); it2 != (*it1).second.end(); it2++)
			{
				if((*it2).second.size())
				{
					actualRanking[i].insert(*(*it2).second.begin());
					(*it2).second.erase((*it2).second.begin());
				}
			}
			if(actualRanking[i].empty())
			{
				actualRanking.erase(i);
				break;
			}
			i++;
		}
		if(!type)
			break;
	}
	
	for(map<int, unordered_set<string> >::iterator it1 = finalRanking.begin(); it1 != finalRanking.end(); it1++)
	{
		found = 0;
		if(actualRanking.find((*it1).first) == actualRanking.end())
			break;
		for(unordered_set<string>::iterator it2 = (*it1).second.begin(); it2 != (*it1).second.end(); it2++)
		{
			if(actualRanking[(*it1).first].find(*it2) != actualRanking[(*it1).first].end())
				found++;
		}
		ranking[(*it1).first].acc += ((float)found/(*it1).second.size())*100;
		ranking[(*it1).first].cnt += 1;
	}
}


void searchOnQueryAcc(string q, bool type)
{
	char word[129];
	int i, glob, found;
	bool flag, flag2;
	unordered_set<string> abc;
	map<int, vector<string> > finalRanking;
	unordered_set<string> added;
	map<string, int> fileCount;
	vector<pairs> fileCountV;

	strcpy((char *)ip, (q).c_str());
	for(i = strlen((char *)ip); i < 128; i++)
		ip[i] = '0';
	for(i = 0; i < 16; i++)
		iv[i] = iv_save[i];
	aes_crypt_cbc( &aes, AES_ENCRYPT, 16, iv, ip, op );
	for(i = 0; i < 128; i++)
	{
		word[i] = op[i];
		if(word[i] == '\0')
			word[i] = '0';
	}
	word[128] = '\0';
	for(i = 0; i < 25; i++)
		counter[i] = 0;
	search(bloomroot, word, 1, 99);
	glob = 1;
	for(map<int, map<int, vector<string> > >::iterator it1 = resultset.begin(); it1 != resultset.end(); it1++)
	{
		if((*it1).first == 99)
			continue;
		flag = true;
		while(flag)
		{
			for(map<int, vector<string> >::iterator it2 = (*it1).second.begin(); it2 != (*it1).second.end(); it2++)
			{
				i = 0;
				while((i < 10) && (*it2).second.size())
				{
					fileCount[*(*it2).second.begin()] += 1;
					(*it2).second.erase((*it2).second.begin());
					i++;
				}
			}
			if(fileCount.empty())
				flag = false;
			for(map<string, int>::iterator it2 = fileCount.begin(); it2 != fileCount.end(); it2++)
			{
				pairs tmp = {(*it2).first, (*it2).second};
				fileCountV.push_back(tmp);
			}
			sort(fileCountV.begin(), fileCountV.end(), mysort);
			i = 0;
			flag2 = false;
			for(vector<pairs>::iterator it2 = fileCountV.begin(); it2 != fileCountV.end(); it2++)
			{
				if(i++ == 10)
					break;
				fileCount.erase((*it2).id);
				if(added.find((*it2).id) == added.end())
				{
					finalRanking[glob].push_back((*it2).id);
					added.insert((*it2).id);
					flag2 = true;
				}
			}
			if(flag2)
				glob++;
			fileCountV.clear();
		}
		if(!type)
			break;			
	}
	resultset.clear();

	for(unordered_map<string, vector<pairs> >::iterator it1 = inverted_table2.begin(); it1 != inverted_table2.end(); it1++)
	{
		if((*it1).first.find(q) != string::npos)
			for(vector<pairs>::iterator it2 = (*it1).second.begin(); it2 != (*it1).second.end(); it2++)
				abc.insert((*it2).id);
	}

	for(map<int, vector<string> >::iterator it1 = finalRanking.begin(); it1 != finalRanking.end(); it1++)
	{
		found = 0;
		for(vector<string>::iterator it2 = (*it1).second.begin(); it2 != (*it1).second.end(); it2++)
			if(abc.find(*it2) != abc.end())
				found++;
		ranking[(*it1).first].acc += ((float)found/(*it1).second.size())*100;
		ranking[(*it1).first].cnt += 1;
	}
}

double getQuery(int num, bool type, bool isRel)
{
	clock_t t0, t1;
	int pos, qsize;
	vector<string> s;
	string q;
	do
	{
		qsize = 0;
		s.clear();
		pos = (int)rand() % keywords.size();
		if(type)
		{
			for(unsigned int i = 0; i < keywords[pos].length()-1; i++)
				for(unsigned int j = i+2; j < keywords[pos].length()+1; j++)
					s.push_back(keywords[pos].substr(i, j-i));
		}
		else
		{
			for(unsigned int j = 2; j < keywords[pos].length()+1; j++)
				s.push_back(keywords[pos].substr(0, j));
		}
		pos = rand() % s.size();
		q = s[pos];
		for(unordered_map<string, vector<pairs> >::iterator it1 = inverted_table2.begin(); it1 != inverted_table2.end(); it1++)
			if((*it1).first.find(q) != string::npos)
				qsize++;
	}while((qsize < num) || (qsize >= num +10));
	t0 = clock();
	if(isRel)
		searchOnQueryRel(q, type);
	else
		searchOnQueryAcc(q, type);
	t1 = clock();
	return (double)(t1 - t0)/CLOCKS_PER_SEC;
}

int main()
{
	int i, fp = 0, pos, len;
	unsigned int val;
	char *s, word[129], str[129];
	clock_t t1, t2;
	vector<string> files;
	set<string> chosenFiles;

	char *pers = (char *)"aes_key_generation";
	int ret;
	double elapsedTime;

	srand(time(NULL));

	ctr_drbg_context ctr_drbg;
	entropy_context entropy;
	entropy_init( &entropy );
	if( ( ret = ctr_drbg_init( &ctr_drbg, entropy_func, &entropy,
			(unsigned char *) pers, strlen( pers ) ) ) != 0 )
	{
		//	    printf( " failed\n ! ctr_drbg_init returned -0x%04x\n", -ret );
	}
	if( ( ret = ctr_drbg_random( &ctr_drbg, key, 32 ) ) != 0 )
	{
		//	    printf( " failed\n ! ctr_drbg_random returned -0x%04x\n", -ret );
	}
	for(i = 0; i < 16; i++)
		iv_save[i] = iv[i] = (char)(i + 40);
	aes_setkey_enc( &aes, key, 128 );

	for(int run = 0; run < 7; run++)
	{
		for(i = 0; i < 5; i++)
		{
			val = rand();
			hashKey[run][i*4] = val & 0xff;
			hashKey[run][i*4+1] = (val>>8) & 0xff;
			hashKey[run][i*4+2] = (val>>16) & 0xff;
			hashKey[run][i*4+3] = (val>>24) & 0xff;
		}
	}
	getPrimes();
	getStopwords();
	getFpWords();

	while(chosenFpWords.size() < 1000)
	{
		pos = (int)rand() % fpWords.size();
		chosenFpWords.insert(fpWords[pos]);
	}

	DIR *mydir = opendir("we");
	struct dirent *entry = NULL;
	
	while((entry = readdir(mydir)))
	{
		s=entry->d_name;
		if(s[0] != '.')
			files.push_back(s);
	}
	closedir(mydir);

	while(chosenFiles.size() < NUM_FILES)
		chosenFiles.insert(files[(int)rand()%files.size()]);

	//for(vector<string>::iterator it = files.begin(); it != files.end(); it++)
	//	chosenFiles.insert(*it);
	for(set<string>::iterator it = chosenFiles.begin(); it != chosenFiles.end(); it++)
	{
		strcpy(word, (*it).c_str());
		getKeywords(word);
	}

	i = 1;
	for(unordered_set<string>::iterator it = init_table.begin(); it != init_table.end(); it++)
	{
		allKeywords.insert(*it);
		if(i++ == NUM_KWS)
			break;
	}
	init_table.clear();

	for(set<string>::iterator it = chosenFiles.begin(); it != chosenFiles.end(); it++)
	{
		strcpy(word, (*it).c_str());
		readfile(word);
	}
	out.open("op1.txt",ios::out);
	out<<inverted_table.size()<<'\t';
	for(map<string, a_list>::iterator it = inverted_table.begin(); it != inverted_table.end(); it++)
		for(vector<pairs>::iterator it2 = (*it).second.docIDs.begin(); it2 != (*it).second.docIDs.end(); it2++)
			(*it2).val = (*it2).val * log(NUM_FILES/(*it).second.docIDs.size());
	for(map<string, a_list>::iterator it = inverted_table.begin(); it != inverted_table.end();)
	{
		string prev = (*it).first;
		for(map<string, a_list>::iterator it2 = it; it2 != inverted_table.end(); it2++)
		{
			if((*it2).first == (*it).first)
				continue;
			if((*it).first == (*it2).first.substr(0, (*it).first.length()))
			{
				vector<pairs>:: iterator it3 = (*it).second.docIDs.begin();
				vector<pairs>:: iterator it4 = (*it2).second.docIDs.begin();
				while(it3 != (*it).second.docIDs.end() && it4 != (*it2).second.docIDs.end())
				{
					if((*it3).id == (*it4).id)
					{
						(*it4).val += (*it3).val;
						it3 = (*it).second.docIDs.erase(it3);
						it4++;
					}
					else if(isLess((*it3).id, (*it4).id))						
						it3++;
					else
						it4++;
				}
				if((*it).second.docIDs.size() == 0)
				{
					map<string, a_list>::iterator it5 = it;
					it++;
					inverted_table.erase(it5);
				}
			}
			else
			{
				it++;
				break;
			}
		}
		if(prev == (*it).first)
			it++;
	}
	out<<inverted_table.size()<<endl;
	for(map<string, a_list>::iterator it = inverted_table.begin(); it != inverted_table.end();it++)
	{
		len = (*it).first.length();
		for(unsigned int k = 0; k < len-1; k++)
		{
			for(unsigned int j = k+2; j < len+1; j++)
			{
				strcpy((char *)ip, (*it).first.substr(k, j-k).c_str());
				for(i = strlen((char *)ip); i < 128; i++)
					ip[i] = '0';
				for(i = 0; i < 16; i++)
					iv[i] = iv_save[i];
				aes_crypt_cbc( &aes, AES_ENCRYPT, 16, iv, ip, op );
				for(i = 0; i < 128; i++)
				{
					str[i] = op[i];
					if(str[i] == '\0')
					str[i] = '0';
				}
				str[128] = '\0';
				substrings[(*it).first].insert(str);
			}
		}
		sort((*it).second.docIDs.begin(), (*it).second.docIDs.end(), mysort);
		inverted_table2[(*it).first] = (*it).second.docIDs;
	}
	t1 = clock();
	createSplitRoot();
	createSplitTree(splitroot);
	t2 = clock();
	out<<(double)(t2 - t1)/CLOCKS_PER_SEC<<" seconds clustering time"<<endl;
	sims.clear();
	bloomroot = new bloomnode;
	createBloomTree(bloomroot, splitroot, 1);
	
	t2 = clock();
	out<<(double)(t2 - t1)/CLOCKS_PER_SEC<<" seconds index formation time"<<endl;
	
	for(map<string, a_list>::iterator it = inverted_table.begin(); it != inverted_table.end(); it++)
		keywords.push_back((*it).first);
	
	out<<subs<<'\t'<<pres<<'\t'<<numdocs<<'\t'<<coeffs<<endl;
	for(set<string>::iterator it = chosenFpWords.begin(); it != chosenFpWords.end(); it++)
	{
		strcpy((char *)ip, (*it).c_str());
		for(i = strlen((char *)ip); i < 128; i++)
			ip[i] = '0';
		for(i = 0; i < 16; i++)
			iv[i] = iv_save[i];
		aes_crypt_cbc( &aes, AES_ENCRYPT, 16, iv, ip, op );
		for(i = 0; i < 128; i++)
		{
			word[i] = op[i];
			if(word[i] == '\0')
				word[i] = '0';
		}
		word[128] = '\0';
		for(i = 0; i < 25; i++)
			counter[i] = 0;
		search(bloomroot, word, 1, 99);
		if(resultset.size() > 0)
			fp++;
		resultset.clear();		
	}
	out<<"\nFP Rate is:\t"<<(float)fp/10.0<<endl;

	for(int run = 10; run <= 100; run += 10)
	{
		out<<"\n"<<run<<" query result size:\n";
		elapsedTime = 0;
		for(i = 0; i < 10; i++)
			elapsedTime += getQuery(run, false, false);
		out<<"Average time for prefix query:\t\t"<<elapsedTime/10.0<<endl;
		out<<"Accuracy:\t"<<(float)(*ranking.begin()).second.acc/(*ranking.begin()).second.cnt<<"\n";
		ranking.clear();
		elapsedTime = 0;
		for(i = 0; i < 10; i++)
			elapsedTime += getQuery(run, false, true);
		out<<"Relative Accuracy:\t"<<(float)(*ranking.begin()).second.acc/(*ranking.begin()).second.cnt<<"\n";
		ranking.clear();

		elapsedTime = 0;
		for(i = 0; i < 10; i++)
			elapsedTime += getQuery(run, true, false);
		out<<"Average time for substring query:\t"<<elapsedTime/10.0<<endl;
		out<<"Accuracy:\t"<<(float)(*ranking.begin()).second.acc/(*ranking.begin()).second.cnt<<"\n";
		ranking.clear();
		elapsedTime = 0;
		for(i = 0; i < 10; i++)
			elapsedTime += getQuery(run, true, true);
		out<<"Relative Accuracy:\t"<<(float)(*ranking.begin()).second.acc/(*ranking.begin()).second.cnt<<"\n";
		ranking.clear();
	}

	out.close();
	return 0;
}
