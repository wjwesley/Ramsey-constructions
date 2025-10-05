
writeClause := proc(filename, C) local clause, v; clause := ""; for v in C do clause := cat(clause, convert(v, string), " "); end do; clause := cat(clause, "0"); writeline(filename, clause); end proc;
treeCardinalityEncoding := proc(r, S, filename, litOffset, allVarTable) local i, j, k, m, n, L, t, s, b, requiredVars, l; n := numelems(S); L := table(); t := table(); if r = 0 then for s in S do writeClause(filename, {-allVarTable[op(s)]}); end do; return ; end if; b := generateBtable(S, allVarTable, litOffset, r); requiredVars := {}; for k to 2*n - 1 do writeClause(filename, {b[k, 0]}); end do; for k from n to 2*n - 1 do L[k] := 1; t[k] := 1; end do; for l to n - 1 do k := n - l; L[k] := L[2*k] + L[2*k + 1]; t[k] := min(r, L[k]); end do; for k to n - 1 do for i to t[2*k] do for j to t[2*k + 1] do if i + j = r + 1 then writeClause(filename, {-b[2*k, i], -b[2*k + 1, j]}); requiredVars := requiredVars union {b[2*k, i], b[2*k + 1, j]}; end if; end do; end do; end do; for k from 2 to n - 1 do for m to t[k] do if member(b[k, m], requiredVars) then for i from 0 to t[2*k] do for j from 0 to t[2*k + 1] do if i + j = m then writeClause(filename, {b[k, m], -b[2*k, i], -b[2*k + 1, j]}); requiredVars := requiredVars union {b[2*k, i], b[2*k + 1, j]}; end if; end do; end do; end if; end do; end do; end proc;

# 

generateBtable := proc(vars, xVals, litOffset, r) local litNum, numVars, b, k, i; litNum := litOffset + 1; numVars := numelems(vars); b := table(); for k to 2*numVars - 1 do for i from 0 to r do if k < numVars or i <> 1 then b[k, i] := litNum; litNum := litNum + 1; else b[k, i] := xVals[op(vars[k - numVars + 1])]; end if; end do; end do; return b; end proc;
xTable := proc(n) local t, litNum, i, j; t := table(); litNum := 1; for i to n do for j from i + 1 to n do t[i, j] := litNum; litNum := litNum + 1; end do; end do; return t; end proc;
NULL;
xTableWithTriangles := proc(n, triOffset) local t, litNum, i, j, k; t := table(); litNum := 1; for i to n do for j from i + 1 to n do t[i, j] := litNum; litNum := litNum + 1; end do; end do; litNum := litNum + triOffset; for i to n do for j from i + 1 to n do for k from j + 1 to n do t[i, j, k, 0] := litNum; t[i, j, k, 1] := litNum + 1; litNum := litNum + 2; end do; end do; end do; return t; end proc;

allAnd3Clauses := proc(n, triOffset) local C, x, i, j, k; C := {}; x := xTableWithTriangles(n, triOffset); for i to n do for j from i + 1 to n do for k from j + 1 to n do C := C union {{x[i, j], -x[i, j, k, 0]}, {x[i, k], -x[i, j, k, 0]}, {x[j, k], -x[i, j, k, 0]}, {-x[i, j], -x[i, j, k, 1]}, {-x[i, k], -x[i, j, k, 1]}, {-x[j, k], -x[i, j, k, 1]}, {x[i, j], x[i, k], x[j, k], x[i, j, k, 1]}, {x[i, j, k, 0], -x[i, j], -x[i, k], -x[j, k]}}; end do; end do; end do; return C; end proc;

bookCardEncoding := proc(n, r, s, filename, shatterOffset) local edgeLitNums, litOffset, C, c, i, j, S, v; fclose(filename); fopen(filename, WRITE); writeline(filename, "p cnf 1 1"); edgeLitNums := xTableWithTriangles(n, shatterOffset); litOffset := 2*binomial(n, 3) + binomial(n, 2) + 1 + shatterOffset; C := allAnd3Clauses(n, shatterOffset); for c in C do writeClause(filename, c); end do; for i to n do for j from i + 1 to n do S := {}; for v in {seq(i, i = 1 .. n)} minus {i, j} do S := S union {[op({i, j, v}), 1]}; end do; treeCardinalityEncoding(r - 1, S, filename, litOffset, edgeLitNums); litOffset := litOffset + (r + 1)*(2*n - 5); end do; end do; for i to n do for j from i + 1 to n do S := {}; for v in {seq(i, i = 1 .. n)} minus {i, j} do S := S union {[op({i, j, v}), 0]}; end do; treeCardinalityEncoding(s - 1, S, filename, litOffset, edgeLitNums); litOffset := litOffset + (s + 1)*(2*n - 5); end do; end do; fclose(filename); end proc;

bookCardEncoding(13, 3, 3, "RB3B3_n13.cnf", 0);
bookCardEncoding(11, 3, 2, "RB2B3_n11.cnf", 0);




