/*
    Quine McCluskey algorithm
    input constraints
        - there are two binary operators: "+, *"
        - binary operators should be surrounded with spaces
        - Valid Parentheses order
        - unary operator "!" precede variable name without spaces
    Valid Inputs:
        !a * !b * !c + !a * !b * c + a * !b * !c + a * !b * c + a * b * !c
        (a + b) * !c
        ...
*/
 
 
 
 
#include <iostream>
#include <map>
#include <string>
#include <vector>
#include <stack>
#include <sstream>
#include <set>
#include <algorithm>
#include <map>
using namespace std;
 
const int INF = 2e9;
map<char, int> preced;
int precedence(char ch) {
    return preced[ch];
}
 
class BoolTable {
    string expr;
    string parsedExpr;
    int varCnt;
    vector<string> variables;
    vector<pair<vector<bool>, bool> > boolTable; // (x1, ..., xn), F
    static const char ONE = '1', ZERO = '0';
 
    const string operators = "+*";
 
    
    string parseExpr(string expr) { // return postfix notation
        vector<string> out;
        stringstream ss; ss << expr;
        string tmp;
        stack<char> oper;
        while (getline(ss, tmp, ' ')) {
            if (tmp[0] == '(') {
                int i = 0;
                for (; i < tmp.size() && tmp[i] == '('; ++i) {
                    oper.push('(');
                }
                tmp.erase(tmp.begin(), tmp.begin() + i);
            }
            if (tmp.back() == ')') {
                int i = tmp.find(')');
                string var;
                var.assign(tmp.begin(), tmp.begin() + i);
                out.push_back(var);
                for (; i < tmp.size(); ++i) {
                    while (oper.top() != '(') {
                        out.push_back(string());
                        out.back().push_back(oper.top());
                        oper.pop();
                    }
                    oper.pop();
                }
                tmp = "";
            }
            if (operators.find(tmp) != std::string::npos) {
                char o1 = tmp[0];
                while (oper.empty() == false && oper.top() != '(' &&
                    (precedence(oper.top()) > precedence(o1)))
                {
                    char o2 = oper.top();
                    oper.pop();
                    out.push_back(string());
                    out.back().push_back(o2);
                }
                oper.push(o1);
            }
            else if (tmp.size() != 0) {
                out.push_back(tmp);
            }
        }
        while (oper.empty() == false) {
            out.push_back(string());
            out.back().push_back(oper.top());
            oper.pop();
        }
        string ans;
        for (auto p : out) {
            ans += p;
            ans.push_back(' ');
        }
        return ans;
    }
    
    // calculate only parsed expr in postfix 
    bool calculateExpr(vector<bool> vec, string _expr) { 
        map<string, bool> _value;
        for (int i = 0; i < vec.size(); ++i)
            _value[variables[i]] = vec[i];
 
        vector<string> _exprVec;
        stringstream ss; ss << _expr;
        string tmp;
        while (getline(ss, tmp, ' ')) {
            if (tmp.size()>0 && (tmp[0]=='!' || isalpha(tmp[0]) || isdigit(tmp[0]) || operators.find(tmp[0]) != std::string::npos))
                _exprVec.push_back(tmp);
        }
        
        for (int i = 0; i < _exprVec.size(); ++i) {
            if (operators.find(_exprVec[i]) != std::string::npos) continue;
            bool flag = false;
            if (_exprVec[i][0] == '!') {
                flag = true;
                _exprVec[i].erase(_exprVec[i].begin());
            }
            if (_value[_exprVec[i]]) {
                _exprVec[i] = string();
                
                if (flag)
                    _exprVec[i].push_back(ZERO);
                else
                    _exprVec[i].push_back(ONE);
            }
            else {
                _exprVec[i] = string();
 
                if (flag)
                    _exprVec[i].push_back(ONE);
                else
                    _exprVec[i].push_back(ZERO);
            }
        }
 
        stack<bool> calc;
        for (int i = 0; i < _exprVec.size(); ++i) {
            if (_exprVec[i].find(ONE) != std::string::npos || _exprVec[i].find(ZERO) != std::string::npos) {
                if (_exprVec[i].find(ONE) != std::string::npos)
                    calc.push(true);
                else
                    calc.push(false);
            }
            else {
                bool a, b;
                a = calc.top(); calc.pop();
                b = calc.top(); calc.pop();
                bool F;
                if (_exprVec[i].find("+") != std::string::npos)
                    F = a || b;
                else
                    F = a && b;
                calc.push(F);
            }
        }
        return calc.top();
    }
    
    vector<bool> calculateBinary(int a) {
        vector<bool> v(varCnt);
        for (int i = 0; i < varCnt; ++i) {
            v[i] = (1 << i) & (a);
        }
        reverse(v.begin(), v.end());
        return v;
    }
 
    // count variables, type them in lexic order in variables array
    void parseVariables(string expr) { // expr - postfix notation string
        int _varCnt = 0;
        vector<string> _expr;
        stringstream ss; ss << expr;
        string tmp;
        set<string> _variables;
        while (getline(ss, tmp, ' ')) {
            _expr.push_back(tmp);
        }
        for (auto str : _expr) {
            if (str.size()>0 && (isalpha(str[0]) || isdigit(str[0]) || str[0]=='!')) {
                if (str.front() == '!') str.erase(str.begin());
                if (_variables.find(str) == _variables.end())
                    ++_varCnt;
                _variables.insert(str);
            }
        }
        varCnt = _varCnt;
        for (auto p : _variables)
            variables.push_back(p);
        sort(variables.begin(), variables.end());
    }
    
    vector<pair<vector<bool>, bool> > createBoolTable() {
        vector<pair<vector<bool>, bool> > _boolTable;
        _boolTable.resize(1 << varCnt);
 
        for (int i = 0; i < _boolTable.size(); ++i)
            _boolTable[i].first = calculateBinary(i);
 
 
 
        for (int i = 0; i < _boolTable.size(); ++i)
            _boolTable[i].second = calculateExpr(_boolTable[i].first, parsedExpr);
        return _boolTable;
    }
public:
    BoolTable(string _expr) {
        expr = _expr;
        parsedExpr = parseExpr(_expr);
        parseVariables(parsedExpr);
        boolTable = createBoolTable();
        
    }
    vector<string> getVariables() {
        return variables;
    }
    void printTable() {
        cout << expr << endl;
        for (int i = 0; i < variables.size(); ++i) {
            cout << variables[i] << ' ';
        }
        cout << 'F' << endl;
        for (int i = 0; i < boolTable.size(); ++i) {
            for (int j = 0; j < boolTable[i].first.size(); ++j)
                cout << boolTable[i].first[j] << ' ';
            cout << boolTable[i].second;
            cout << endl;
        }
    }
    int getVariablesCnt() {
        return varCnt;
    }
    bool getFuncValue(int i) {
        return boolTable[i].second;
    }
    
};
pair<int, int> difference(string a, string b) { // count last id of differnet values and amount of differneces (dif, id)
    pair<int, int> dif(0, 0);
    for (int i = 0; i < a.size(); ++i) {
        //if (a[i] == '*' || b[i] == '*') continue;
        if (a[i] != b[i]) {
            dif.first++;
            dif.second = i;
        }
    }
    return dif;
}
int countOnes(string a) {
    int tmp = 0;
    for (int i = 0; i < a.size(); ++i)
        if (a[i] == '1') ++tmp;
    return tmp;
}
 
bool isCover(string minterm, string implicant);
int countRang(set<string> impl);
pair<int, set<string> > minimize(const vector<string>& minterms, const vector<string>& implicants, string req, int varCnt);
set<string> getImplicants(set<string> minterms, int varCnt);
 
string convert(string implicant, const vector<string>& variables) {
    string ret;
    for (int i = 0; i < implicant.size(); ++i) {
        if (implicant[i] == '0') {
            ret.push_back('!');
            ret += variables[i];
        }
        if (implicant[i] == '1') {
            ret += variables[i];
        }
    }
    return ret;
}
string quine_McCluskey_algorithm(set<string> minterms, const vector<string>& variables,  int varCnt) {
    set<string> implicants = getImplicants(minterms, varCnt);
    vector<string> implicantsVec;
    vector<string> mintermsVec;
    for (auto p : implicants) {
        implicantsVec.push_back(p);
    }
    for (auto p : minterms) {
        mintermsVec.push_back(p);
    }
    string req = "";
    set<string> minimized = minimize(mintermsVec, implicantsVec, req, varCnt).second;
    vector<string> tmpImplicants;
    for (auto p : minimized) {
        tmpImplicants.push_back(convert(p, variables));
    }
    string ans = "";
    for (int i = 0; i < tmpImplicants.size(); ++i){
        ans += tmpImplicants[i];
        if (i != tmpImplicants.size() - 1) {
            string oper = " + ";
            ans += oper;
        }
    }
    return ans;
}
 
bool isCover(string minterm, string implicant) {
    bool ans = true;
    for (int i = 0; i < minterm.size(); ++i) {
        if (implicant[i] != '-') {
            ans &= minterm[i] == implicant[i];
        }
    }
    return ans;
}
int countRang(set<string> impl) {
    int r = 0;
    for (auto p : impl) {
        for (int i = 0; i < p.size(); ++i) {
            if (p[i] == '1' || p[i] == '0') {
                ++r;
            }
        }
    }
    return r;
}
pair<int, set<string> > minimize(const vector<string>& minterms, const vector<string>& implicants, string req, int varCnt) {
    
    map<string, bool> used;
    set<string> usingImplicants;
    for (int i = 0; i < req.size(); ++i) {
        if (req[i] == '1') {
            usingImplicants.insert(implicants[i]);
        }
    }
    for (int i = 0; i < minterms.size(); ++i) {
        bool flag = false;
        for (auto imp : usingImplicants) {
            flag |= isCover(minterms[i], imp);
        }
        used[minterms[i]] = flag;
    }
    bool isAllCover = true;
    for (auto p : minterms) {
        isAllCover &= used[p];
    }
    if (isAllCover) {
        int rang = countRang(usingImplicants);
        return make_pair(rang, usingImplicants);
    }
    else {
        if (req.size() >= implicants.size()) {
            return make_pair(INF, set<string>());
        }
        string tmpLeft = req;
        tmpLeft.push_back('0');
        auto left = minimize(minterms, implicants, tmpLeft, varCnt);
        
        string tmpRight = req;
        tmpRight.push_back('1');
        auto right = minimize(minterms, implicants, tmpRight, varCnt);
        if (left.first < right.first) {
            return left;
        }
        else {
            return right;
        }
    }
}
set<string> getImplicants(set<string> minterms, int varCnt) {
    bool is_end = true;
 
    map<string, bool> used;
    set<string> newMinterms;
    vector<vector<string> > groups(varCnt + 1);
    for (auto p : minterms) {
        groups[countOnes(p)].push_back(p);
    }
    bool flag;
    for (int group = 0; group < varCnt; ++group) {
        for (int i = 0; i < groups[group].size(); ++i) {
            string a = groups[group][i];
 
            if (a.back() == '*') {
                newMinterms.insert(a);
                continue;
            }
 
            flag = true;
            for (int j = 0; j < groups[group + 1].size(); ++j) {
                string b = groups[group + 1][j];
                string tmpa = a;
                pair<int, int> dif = difference(tmpa, b);
                if (dif.first == 1) {
                    used[a] = used[b] = true;
                    tmpa[dif.second] = b[dif.second] = '-';
                    newMinterms.insert(b);
                    flag = false;
 
                }
            }
            is_end &= flag;
 
            if (flag && !used[a]) {
                a.push_back('*');
                newMinterms.insert(a);
            }
        }
    }
    if (is_end) {
        set<string> st;
        for (auto p : minterms) {
            if (p.back() == '*') {
                string tmp;
                tmp.assign(p.begin(), p.end() - 1);
                //minterms.erase(p);
                st.insert(tmp);
            }
            else {
                st.insert(p);
            }
        }
 
        return st;
    }//return minterms
    return getImplicants(newMinterms, varCnt);
 
}
 
int32_t main() {
    preced['+'] = 1;
    preced['*'] = 2;
    
    string expr;
    getline(cin, expr);
    BoolTable table(expr);
    //table.printTable();
    
    set<string> minterms;
    int n = table.getVariablesCnt();
    for (int i = 0; i < (1 << n); ++i) {
        if (table.getFuncValue(i)) {
            string tmp;
            tmp.resize(n);
            for (int j = 0; j < n; ++j) {
                bool flag = (1 << j) & (i);
                tmp[j] = (flag?'1':'0');
            }
            reverse(tmp.begin(), tmp.end());
            minterms.insert(tmp);
        }
    }
    
    
    string ans = quine_McCluskey_algorithm(minterms, table.getVariables(), table.getVariablesCnt());
    cout << ans;
 
    
}
