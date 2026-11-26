-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.scan_owned_literal_rows
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-26T03:38:39.463604+00:00
-- url     : https://prove2.me/submissions/3051c10a-0283-4183-8755-cca3fecceb63

import Definitions.Def_StableMSR_RegionalMenuImage
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option maxHeartbeats 4100000
set_option maxRecDepth 35000
set_option autoImplicit false

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 35000
private theorem source_loop {N:ℕ} {input:ℤ → ℤ} (ix last n cap:ℕ) (body:Program) (P:ℕ→State→Prop) (ne:ix≠last)
    (step:∀i < n,∀s:State,P i s → s.reg ix=(i:ℤ) → s.reg last=(n:ℤ)-1 →
      ∃t k,Executes N input body s t k ∧ k≤cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) (t.assign ix (t.reg ix+1)))
    (i rem:ℕ) (len:i+rem=n) (s:State) (start:P i s) (idx:s.reg ix=(i:ℤ)) (lim:s.reg last=(n:ℤ)-1) :
    ∃t k,Executes N input (.loop ix last (chain [body,.op (.regular (.inc ix))])) s t k ∧ k≤1+rem*(cap+5) ∧ P n t :=by
  induction rem generalizing i s with
  | zero=>
    have eq:i=n:=by omega
    exact ⟨s,1,.stop (by rw [idx,lim];omega),by omega,eq ▸ start⟩
  | succ r ih=>
    have lt:i < n:=by omega
    obtain ⟨u,k,ex,tim,idx',lim',next⟩:=step i lt s start idx lim
    let v:=u.assign ix (u.reg ix+1)
    have vi:v.reg ix=((i+1:ℕ):ℤ):=by simp [v,State.assign,idx',idx]
    have vl:v.reg last=(n:ℤ)-1:=by simp [v,State.assign,Ne.symm ne,lim',lim]
    obtain ⟨t,z,more,tm,out⟩:=ih (i+1) (by omega) v next vi vl
    have full:Executes N input (chain [body,.op (.regular (.inc ix))]) s v (1+k+(1+1+1)):=.seq ex (.seq (.op rfl) (.skip _))
    exact ⟨t,_,.more (by rw [idx,lim];omega) full more,by rw [Nat.succ_mul];omega,out⟩

private def forSetup (ix last len:ℕ) (s:State) := let u:=s.assign ix 0; let v:=u.assign last (u.reg len);v.assign last (v.reg last-1)
private theorem source_for {N:ℕ} {input:ℤ → ℤ} (ix last len n cap:ℕ) (body:Program) (P:ℕ→State→Prop)
    (ne:ix≠last) (dis:len≠ix) (s:State) (size:s.reg len=(n:ℤ))
    (start:P 0 (forSetup ix last len s))
    (step:∀i < n,∀s:State,P i s → s.reg ix=(i:ℤ) → s.reg last=(n:ℤ)-1 →
      ∃t k,Executes N input body s t k ∧ k≤cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) (t.assign ix (t.reg ix+1))) :
    ∃t k,Executes N input (forCount ix last len body) s t k ∧ k≤9+n*(cap+5) ∧ P n t :=by
  let u:=forSetup ix last len s
  have fi:u.reg ix=0:=by simp [u,forSetup,State.assign,ne]
  have last':u.reg last=(n:ℤ)-1:=by simp [u,forSetup,State.assign,dis,size]
  obtain ⟨t,z,loop,tm,out⟩:=source_loop ix last n cap body P ne step 0 n (by omega) u start fi last'
  refine ⟨t,_,.seq (.op rfl) (.seq (.op rfl) (.seq (.op rfl) (.seq loop (.skip _)))),by omega,out⟩


end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
private def writesOp (j:ℕ) : Operation → Bool
  | .regular (.store _ _)|.save _ _ _=>false
  | .regular (.set d _)|.regular (.copy d _)|.regular (.add d _ _)|.regular (.sub d _ _)|
    .regular (.inc d)|.regular (.dec d)|.regular (.load d _)|.multiply d _ _|.divide _ d _ _|
    .fetch d _ _|.shift d _ _=>j==d
  | .alloc d _=>j==d || j==8
  | .output=>j==82
private def writesReg (j:ℕ) : Program → Bool
  | .skip=>false | .op o=>writesOp j o | .seq p q|.cond _ _ p q=>writesReg j p || writesReg j q
  | .loop _ _ p=>writesReg j p
private theorem op_preserves {n input s t k} (o:Operation) (j:ℕ) (frame:writesOp j o=false)
    (ex:o.next n input s=some (t,k)):t.reg j=s.reg j:=by
  cases o with
  | regular o=>
    cases o <;> simp [writesOp] at frame <;> simp only [Operation.next,regularNext] at ex <;>
      (try split at ex) <;> (try contradiction) <;> obtain ⟨rfl,rfl⟩:=Option.some.inj ex <;> simp [State.assign,frame]
  | multiply|divide|shift|fetch|save|alloc|output=>
    simp [writesOp] at frame
    simp only [Operation.next] at ex
    (try split at ex) <;> (try contradiction) <;> obtain ⟨rfl,rfl⟩:=Option.some.inj ex <;>
      simp_all [State.assign,State.clear,State.save]
private theorem Executes.preserves {n input p s t k} (ex:Executes n input p s t k) (j:ℕ) (off:writesReg j p=false):
    t.reg j=s.reg j:=by
  induction ex with
  | skip|stop=>rfl
  | op h=>exact op_preserves _ _ off h
  | seq _ _ ih jh=>obtain ⟨a,b⟩:=Bool.or_eq_false_iff.mp off;exact (jh b).trans (ih a)
  | yes _ _ ih=>exact ih (Bool.or_eq_false_iff.mp off).1
  | no _ _ ih=>exact ih (Bool.or_eq_false_iff.mp off).2
  | more _ _ _ ih jh=>exact (jh off).trans (ih off)
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
private lemma outside_for {ix last len r : ℕ} {body : Program}
    (off : writesReg r (forCount ix last len body) = false) :
    r ≠ ix ∧ r ≠ last ∧ writesReg r body = false := by
  simpa [forCount,chain,writesReg,writesOp,and_assoc,and_left_comm,and_comm] using off

private lemma counted {n : ℕ} {m : ℤ → ℤ} (ix last len count cap : ℕ) (body : Program)
    (s : State) (P : ℕ → State → Prop) (ne : ix ≠ last) (dis : len ≠ ix)
    (ixSafe : writesReg ix body = false) (lastSafe : writesReg last body = false)
    (size : s.reg len = (count : ℤ)) (init : P 0 s)
    (ignores : ∀ j u a v, a = ix ∨ a = last → P j u → P j (u.assign a v))
    (step : ∀ i < count, ∀ u, P i u →
      (∀ r, writesReg r (forCount ix last len body) = false → u.reg r = s.reg r) →
      u.reg ix = (i : ℤ) → ∃ t k, Executes n m body u t k ∧ k ≤ cap ∧ P (i+1) t) :
    ∃ t k, Executes n m (forCount ix last len body) s t k ∧
      k ≤ 9+count*(cap+5) ∧ P count t := by
  let Q := fun j u => P j u ∧ ∀ r, writesReg r (forCount ix last len body) = false → u.reg r = s.reg r
  have start : Q 0 (forSetup ix last len s) := by
    refine ⟨ignores _ _ _ _ (.inr rfl) (ignores _ _ _ _ (.inr rfl) (ignores _ _ _ _ (.inl rfl) init)),?_⟩
    intro r off
    obtain ⟨a,b,_⟩ := outside_for off
    simp [forSetup,State.assign,a,b]
  obtain ⟨t,k,run,tm,res,_⟩ := source_for (N:=n) (input:=m) ix last len count cap body Q ne dis s size start (by
    intro i hi u good idx _
    obtain ⟨t,k,ex,tm,next⟩ := step i hi u good.1 good.2 idx
    refine ⟨t,k,ex,tm,ex.preserves _ ixSafe,ex.preserves _ lastSafe,ignores _ _ _ _ (.inl rfl) next,?_⟩
    intro r off
    obtain ⟨a,_,b⟩ := outside_for off
    simpa [State.assign,a] using (ex.preserves r b).trans (good.2 r off))
  exact ⟨t,k,run,tm,res⟩


end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
private inductive PrefixRun (N:ℕ) (input:ℤ → ℤ) : List Program → State → State → ℕ → Prop where
  | nil (s:State) : PrefixRun N input [] s s 0
  | cons {p ps s u t a z} : Executes N input p s u a → PrefixRun N input ps u t z →
    PrefixRun N input (p::ps) s t (1+a+z)
private theorem PrefixRun.continue {N input ps s t z} (h:PrefixRun N input ps s t z)
    (q:Program) {u k} (tail:Executes N input q t u k):
    Executes N input (ps.foldr Program.seq q) s u (z+k):=by
  induction h with
  | nil=>simpa using tail
  | cons run _ ih=>
    simpa [Nat.add_assoc] using Executes.seq run (ih tail)
private theorem PrefixRun.finish {N input ps s t z} (h:PrefixRun N input ps s t z):
    Executes N input (chain ps) s t (z+1):=h.continue .skip (.skip t)
private theorem splitChain {N input} (ps:List Program) {s t:State} {k:ℕ} (ex:Executes N input (chain ps) s t k) :
    ∃z,PrefixRun N input ps s t z ∧ k=z+1:=by
  induction ps generalizing s t k with
  | nil=>cases ex;exact ⟨0,.nil _,rfl⟩
  | cons p ps ih=>
    change Executes N input (.seq p (chain ps)) s t k at ex
    cases ex with
    | seq left right=>
      obtain ⟨z,e,h⟩:=ih right
      exact ⟨_,.cons left e,by omega⟩
private def evalLine (n:ℕ) (m:ℤ → ℤ) : Program → State → Option (State×ℕ)
  | .skip,s=>some (s,1)
  | .op o,s=>o.next n m s
  | .seq p q,s=>do
    let (u,a)←evalLine n m p s
    let (t,b)←evalLine n m q u
    pure (t,1+a+b)
  | .cond i j p q,s=>do
    let (t,b)←if s.reg i ≤ s.reg j then evalLine n m p s else evalLine n m q s
    pure (t,1+b)
  | .loop _ _ _,_=>none
private theorem evalLine_sound {n m} (p:Program) (s t:State) (k:ℕ) (ex:evalLine n m p s=some (t,k)):
    Executes n m p s t k:=by
  induction p generalizing s t k with
  | skip=>obtain ⟨rfl,rfl⟩:=Option.some.inj ex;exact .skip _
  | op=>exact .op ex
  | loop=>contradiction
  | seq p q a b=>
    cases h:evalLine n m p s with
    | none=>simp [evalLine,h] at ex
    | some z=>
      obtain ⟨u,au⟩:=z
      cases j:evalLine n m q u with
      | none=>simp [evalLine,h,j] at ex
      | some v=>obtain ⟨v,bu⟩:=v;simp [evalLine,h,j] at ex;obtain ⟨rfl,rfl⟩:=ex
                exact .seq (a _ _ _ h) (b _ _ _ j)
  | cond i j p q a b=>
    by_cases g:s.reg i ≤ s.reg j
    · cases h:evalLine n m p s with
      | none=>simp [evalLine,g,h] at ex
      | some z=>obtain ⟨u,au⟩:=z;simp [evalLine,g,h] at ex;obtain ⟨rfl,rfl⟩:=ex;exact .yes g (a _ _ _ h)
    · cases h:evalLine n m q s with
      | none=>simp [evalLine,g,h] at ex
      | some z=>obtain ⟨u,au⟩:=z;simp [evalLine,g,h] at ex;obtain ⟨rfl,rfl⟩:=ex;exact .no g (b _ _ _ h)


private def litOpen : List Program := [.op (.multiply 906 226 70),.op (.regular (.add 905 906 227)),
  .op (.multiply 904 905 64),.op (.regular (.copy 228 904))]
private def litOwner : List Program := [.op (.fetch 914 72 229),
  .cond 914 226 (.cond 226 914 (.op (.regular (.set 913 1))) (.op (.regular (.set 913 0)))) (.op (.regular (.set 913 0)))]
private def litGuard : List Program := [.op (.regular (.add 923 228 234)),.op (.fetch 921 77 923),.op (.regular (.copy 920 921)),
  .cond 6 920 (chain [.op (.regular (.add 929 228 234)),.op (.fetch 927 78 929),
    .cond 927 229 (.cond 229 927 (.op (.regular (.set 926 1))) (.op (.regular (.set 926 0)))) (.op (.regular (.set 926 0))),
    .op (.regular (.copy 920 926))]) .skip]
private def litSetup : List Program := [.op (.regular (.set 934 0)),.op (.regular (.set 935 0)),.op (.regular (.add 939 228 234)),
  .op (.multiply 938 939 64),.op (.regular (.add 936 80 938)),.op (.regular (.copy 218 934)),
  .op (.regular (.copy 219 935)),.op (.regular (.copy 220 936))]
private def writeLit := chain (litSetup++[.op .output,.op (.regular (.copy 933 222))])
private def innerLit := chain (litGuard++[.cond 6 920 writeLit .skip])
private def innerSweep := forCount 234 919 64 innerLit
private def outerLit := chain (litOwner++[.cond 6 913 innerSweep .skip])
private def outerSweep := forCount 229 912 64 outerLit

private lemma oneLiteral (n row q mat : ℕ) (m : ℤ→ℤ) (s : State) (bit : ℕ→Bool)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (base : s.reg 228=(row:ℤ))
    (idx : s.reg 234=(q:ℤ)) (matrix : s.reg 80=(mat:ℤ))
    (ready : s.closed=false) (count : s.reg 82=(s.output.length:ℤ))
    (bitmap : ∀p<n,s.heap (mat+((row+q)*n+p))=if bit p then 1 else 0) :
    ∃t k,Executes n m writeLit s t k ∧ k  ≤  250+n*(171+6*n) ∧ t.heap=s.heap ∧ t.closed=false ∧
      t.reg 82=(t.output.length:ℤ) ∧ t.output=s.output++[.lit ((List.range n).filter bit)] := by
  let addr := mat+(row+q)*n
  let u := (((((((s.assign 934 0).assign 935 0).assign 939 ((row+q:ℕ):ℤ)).assign 938 (((row+q)*n:ℕ):ℤ)).assign 936 (addr:ℤ)).assign 218 0).assign 219 0).assign 220 (addr:ℤ)
  have first : Executes n m (chain litSetup) s u (24+6*n) := by
    apply evalLine_sound
    simp [litSetup,chain,evalLine,Operation.next,regularNext,u,addr,State.assign,one,size,base,idx,matrix,show 0 ≤ (row:ℤ)+q by omega]
    all_goals omega
  have h1 := (first.preserves 6 (by decide)).trans one
  have sz := (first.preserves 64 (by decide)).trans size
  have ct := (first.preserves 82 (by decide)).trans count
  have bits (i : ℕ) (hi:i<n) : u.heap (addr+i)=if bit i then 1 else 0 := by
    simpa only [addr,Nat.add_assoc,show u.heap=s.heap from rfl] using bitmap i hi
  have tag : u.reg 218=0 := by simp [u,State.assign]
  have arg : u.reg 219=0 := by simp [u,State.assign]
  have ptr : u.reg 220=(addr:ℤ) := by simp [u,State.assign]
  have recEq : record n u=.lit ((List.range n).filter bit) := by
    simp only [record,tag,if_true,ptr,Int.toNat_natCast]
    congr 1;apply List.filter_congr;intro i hi
    rw [bits i (List.mem_range.mp hi)];cases bit i <;> decide
  have ok : u.bitsOK n (.lit ((List.range n).filter bit))=true := by
    simp only [State.bitsOK,ptr,Int.natCast_nonneg,decide_true,Bool.true_and,Int.toNat_natCast,List.all_eq_true]
    intro i hi;rw [bits i (List.mem_range.mp hi)];cases bit i <;> decide
  let y : State := {u.assign 82 (u.reg 82+1) with output:=u.output++[.lit ((List.range n).filter bit)]}
  have emit : Executes n m (.op .output) u y (200+n*(165+6*n)) := by
    apply Executes.op;simp only [Operation.next,recEq]
    have ur : u.closed=false := ready
    have uc : u.reg 82=(u.output.length:ℤ) := ct
    simp [ur,h1,sz,uc,tag,arg,Instr.tag,Instr.arg,ok,y]
  let t := y.assign 933 (y.reg 222)
  obtain ⟨w,pre,eq⟩:=splitChain litSetup first
  exact ⟨t,_,pre.continue _ (.seq emit (.seq (.op rfl) (.skip _))),by ring_nf at *;omega,
    rfl,ready,by simp [t,y,State.assign,ct,u,count],rfl⟩

private lemma guardLiteral (n row q i rep least : ℕ) (m : ℤ→ℤ) (s : State) (flag : Bool) (low : ℕ)
    (one : s.reg 6=1) (base : s.reg 228=(row:ℤ)) (idx : s.reg 234=(q:ℤ)) (outer : s.reg 229=(i:ℤ))
    (rp : s.reg 77=(rep:ℤ)) (lp : s.reg 78=(least:ℤ))
    (rr : s.heap (rep+(row+q))=if flag then 1 else 0)
    (ll : flag=true → s.heap (least+(row+q))=(low:ℤ)) :
    ∃t k,Executes n m (chain litGuard) s t k ∧ k ≤ 160 ∧ (1  ≤  t.reg 920 ↔ flag=true ∧ low=i) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  let res := (evalLine n m (chain litGuard) s).getD (s,0)
  have rn : 0 ≤ (rep:ℤ)+(row+q) := by omega
  have ln : 0 ≤ (least:ℤ)+(row+q) := by omega
  have ri : ((rep:ℤ)+(row+q)).toNat=rep+(row+q) := by omega
  have li : ((least:ℤ)+(row+q)).toNat=least+(row+q) := by omega
  refine ⟨res.1,res.2,evalLine_sound _ _ _ _ ?_,?_,?_,?_,?_,?_⟩ <;>
    cases flag <;> simp only [Bool.false_eq_true,reduceIte,if_false,if_true,true_implies] at rr ll <;>
    by_cases a : low ≤ i <;> by_cases b : i ≤ low <;>
    simp [res,litGuard,chain,evalLine,Operation.next,regularNext,State.assign,one,base,idx,outer,rp,lp,rn,ln,ri,li,rr,ll,a,b] <;> omega

private lemma ownerLiteral (n i v owner : ℕ) (m : ℤ→ℤ) (s : State) (who : ℕ)
    (idx : s.reg 229=(i:ℤ)) (vertex : s.reg 226=(v:ℤ)) (ptr : s.reg 72=(owner:ℤ))
    (cell : s.heap (owner+i)=(who:ℤ)) :
    ∃t k,Executes n m (chain litOwner) s t k ∧ k ≤ 80 ∧ (1  ≤  t.reg 913 ↔ who=v) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  let res := (evalLine n m (chain litOwner) s).getD (s,0)
  have nn : 0 ≤ (owner:ℤ)+i := by omega
  have ad : ((owner:ℤ)+i).toNat=owner+i := by omega
  refine ⟨res.1,res.2,evalLine_sound _ _ _ _ ?_,?_,?_,?_,?_,?_⟩ <;>
    by_cases a : who ≤ v <;> by_cases b : v ≤ who <;> simp [res,litOwner,chain,evalLine,Operation.next,regularNext,State.assign,idx,vertex,ptr,nn,ad,cell,a,b] <;> omega

private structure LitData (n row rep least mat : ℕ) (s : State) (marked : ℕ→Bool) (low : ℕ→ℕ) (bit : ℕ→ℕ→Bool) : Prop where
  reps : ∀q<n,s.heap (rep+(row+q))=if marked q then 1 else 0
  mins : ∀q<n,marked q=true → s.heap (least+(row+q))=(low q:ℤ)
  bits : ∀q<n,marked q=true → ∀p<n,s.heap (mat+((row+q)*n+p))=if bit q p then 1 else 0
private theorem LitData.keep {n row rep least mat s marked low bit} {t : State} (d : LitData n row rep least mat s marked low bit)
    (h : t.heap=s.heap) : LitData n row rep least mat t marked low bit :=
  ⟨by simpa only [h] using d.reps,by simpa only [h] using d.mins,by simpa only [h] using d.bits⟩
private def emitRow (n i : ℕ) (marked : ℕ→Bool) (low : ℕ→ℕ) (bit : ℕ→ℕ→Bool) (q : ℕ) : Option Instr :=
  if marked q && low q==i then some (.lit ((List.range n).filter (bit q))) else none
private def emitOwner (n v : ℕ) (who : ℕ→ℕ) (marked : ℕ→Bool) (low : ℕ→ℕ) (bit : ℕ→ℕ→Bool) (i : ℕ) :=
  if who i=v then (List.range n).filterMap (emitRow n i marked low bit) else []

private lemma innerLiteral (n row q i rep least mat : ℕ) (m : ℤ→ℤ) (s : State)
    (marked : ℕ→Bool) (low : ℕ→ℕ) (bit : ℕ→ℕ→Bool) (hq:q<n) (D : LitData n row rep least mat s marked low bit)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (base : s.reg 228=(row:ℤ))
    (idx : s.reg 234=(q:ℤ)) (outer : s.reg 229=(i:ℤ)) (rp : s.reg 77=(rep:ℤ)) (lp : s.reg 78=(least:ℤ)) (mp : s.reg 80=(mat:ℤ))
    (ready : s.closed=false) (count : s.reg 82=(s.output.length:ℤ)) :
    ∃t k,Executes n m innerLit s t k ∧ k ≤ 420+n*(171+6*n) ∧ t.heap=s.heap ∧ t.closed=false ∧
      t.reg 82=(t.output.length:ℤ) ∧ t.output=s.output++(emitRow n i marked low bit q).toList := by
  obtain ⟨a,k,guard,tm,test,h,o,c⟩:=guardLiteral n row q i rep least m s (marked q) (low q)
    one base idx outer rp lp (D.reps q hq) (D.mins q hq)
  obtain ⟨w,pre,eq⟩:=splitChain litGuard guard
  have a1:=(guard.preserves 6 (by decide)).trans one
  have ct : a.reg 82=(a.output.length:ℤ) := by rw [o];exact (guard.preserves 82 (by decide)).trans count
  by_cases ok : marked q=true ∧ low q=i
  · obtain ⟨v,l,run,bt,h',c',cn,out⟩:=oneLiteral n row q mat m a (bit q) a1 ((guard.preserves 64 (by decide)).trans size)
      ((guard.preserves 228 (by decide)).trans base) ((guard.preserves 234 (by decide)).trans idx) ((guard.preserves 80 (by decide)).trans mp)
      (c.trans ready) ct (by simpa only [h] using D.bits q hq ok.1)
    exact ⟨v,_,pre.continue _ (.seq (.yes (a1 ▸ test.mpr ok) run) (.skip _)),by omega,h'.trans h,c',cn,
      by simpa [emitRow,ok.1,ok.2,o] using out⟩
  · exact ⟨a,_,pre.continue _ (.seq (.no (by rw [a1];exact fun y=>ok (test.mp y)) (.skip _)) (.skip _)),by omega,
      h,c.trans ready,ct,by simpa [emitRow,ok] using o⟩

private lemma literalSweep (n row i rep least mat : ℕ) (m : ℤ→ℤ) (s : State)
    (marked : ℕ→Bool) (low : ℕ→ℕ) (bit : ℕ→ℕ→Bool) (D : LitData n row rep least mat s marked low bit)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (base : s.reg 228=(row:ℤ)) (outer : s.reg 229=(i:ℤ))
    (rp : s.reg 77=(rep:ℤ)) (lp : s.reg 78=(least:ℤ)) (mp : s.reg 80=(mat:ℤ))
    (ready : s.closed=false) (count : s.reg 82=(s.output.length:ℤ)) :
    ∃t k,Executes n m innerSweep s t k ∧ k ≤ 9+n*(425+n*(171+6*n)) ∧ t.heap=s.heap ∧ t.closed=false ∧
      t.reg 82=(t.output.length:ℤ) ∧ t.output=s.output++(List.range n).filterMap (emitRow n i marked low bit) := by
  let P := fun j (t:State)=>t.heap=s.heap ∧ t.closed=false ∧ t.reg 82=(t.output.length:ℤ) ∧
    t.output=s.output++(List.range j).filterMap (emitRow n i marked low bit)
  obtain ⟨t,k,ex,tm,res⟩:=GeometryTables.counted 234 919 64 n (420+n*(171+6*n)) innerLit s P
    (by decide) (by decide) (by decide) (by decide) size (by simp [P,ready,count]) (by
      intro j u r v eq good;rcases eq with rfl|rfl <;> simpa [P,State.assign] using good) (by
      intro j hj u good fr idx
      obtain ⟨h,c,cn,o⟩:=good
      obtain ⟨v,l,ex,tm,h',c',cn',out⟩:=innerLiteral n row j i rep least mat m u marked low bit hj (D.keep h)
        ((fr 6 (by decide)).trans one) ((fr 64 (by decide)).trans size) ((fr 228 (by decide)).trans base) idx
        ((fr 229 (by decide)).trans outer) ((fr 77 (by decide)).trans rp) ((fr 78 (by decide)).trans lp) ((fr 80 (by decide)).trans mp) c cn
      refine ⟨v,l,ex,tm,h'.trans h,c',cn',?_⟩
      rw [out,o,List.range_succ,List.filterMap_append,List.append_assoc]
      cases eq:emitRow n i marked low bit j <;> simp [eq])
  exact ⟨t,k,ex,by ring_nf at tm ⊢;exact tm,res⟩

private lemma outerLiteral (n row v i owner rep least mat : ℕ) (m : ℤ→ℤ) (s : State)
    (who low : ℕ→ℕ) (marked : ℕ→Bool) (bit : ℕ→ℕ→Bool) (hi:i<n) (D : LitData n row rep least mat s marked low bit)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (base : s.reg 228=(row:ℤ)) (idx : s.reg 229=(i:ℤ))
    (vertex : s.reg 226=(v:ℤ)) (optr : s.reg 72=(owner:ℤ)) (rp : s.reg 77=(rep:ℤ)) (lp : s.reg 78=(least:ℤ)) (mp : s.reg 80=(mat:ℤ))
    (cell : s.heap (owner+i)=(who i:ℤ)) (ready : s.closed=false) (count : s.reg 82=(s.output.length:ℤ)) :
    ∃t k,Executes n m outerLit s t k ∧ k ≤ 95+n*(425+n*(171+6*n)) ∧ t.heap=s.heap ∧ t.closed=false ∧
      t.reg 82=(t.output.length:ℤ) ∧ t.output=s.output++emitOwner n v who marked low bit i := by
  obtain ⟨a,k,g,tm,test,h,o,c⟩:=ownerLiteral n i v owner m s (who i) idx vertex optr cell
  obtain ⟨w,pre,eq⟩:=splitChain litOwner g
  have a1:=(g.preserves 6 (by decide)).trans one
  have ct : a.reg 82=(a.output.length:ℤ) := by rw [o];exact (g.preserves 82 (by decide)).trans count
  by_cases ok : who i=v
  · obtain ⟨t,l,run,bt,h',c',cn,out⟩:=literalSweep n row i rep least mat m a marked low bit (D.keep h)
      a1 ((g.preserves 64 (by decide)).trans size) ((g.preserves 228 (by decide)).trans base) ((g.preserves 229 (by decide)).trans idx)
      ((g.preserves 77 (by decide)).trans rp) ((g.preserves 78 (by decide)).trans lp) ((g.preserves 80 (by decide)).trans mp) (c.trans ready) ct
    exact ⟨t,_,pre.continue _ (.seq (.yes (a1 ▸ test.mpr ok) run) (.skip _)),by omega,h'.trans h,c',cn,by simpa [emitOwner,ok,o] using out⟩
  · exact ⟨a,_,pre.continue _ (.seq (.no (by rw [a1];exact fun y=>ok (test.mp y)) (.skip _)) (.skip _)),by omega,
      h,c.trans ready,ct,by simpa [emitOwner,ok] using o⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open Scene.CutTraversal
theorem solution (n M v j owner rep least matrix : ℕ) (m : ℤ→ℤ) (s : Logical.State)
    (who low : ℕ→ℕ) (marked : ℕ→Bool) (member : ℕ→ℕ→Bool)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ)) (slots : s.reg 70=(M:ℤ))
    (vertex : s.reg 226=(v:ℤ)) (word : s.reg 227=(j:ℤ))
    (ownAt : s.reg 72=(owner:ℤ)) (repAt : s.reg 77=(rep:ℤ)) (minAt : s.reg 78=(least:ℤ))
    (matAt : s.reg 80=(matrix:ℤ)) (ready : s.closed=false) (count : s.reg 82=(s.output.length:ℤ))
    (ownership : ∀q<n,s.heap (owner+q)=(who q:ℤ))
    (reps : ∀q<n,s.heap (rep+((v*M+j)*n+q))=if marked q then 1 else 0)
    (minima : ∀q<n,marked q=true → s.heap (least+((v*M+j)*n+q))=(low q:ℤ))
    (bitmap : ∀q<n,marked q=true → ∀p<n,s.heap (matrix+(((v*M+j)*n+q)*n+p))=if member q p then 1 else 0) :
    ∃t k, Logical.Executes n m (chain ((listOf src_trial).take 5)) s t k ∧ k  ≤  500*(M+1)+500*(n+1)^4 ∧
      t.heap=s.heap ∧ t.closed=false ∧ t.reg 82=(t.output.length:ℤ) ∧
      t.output=s.output++(List.range n).flatMap (fun i=> if who i=v then
        (List.range n).filterMap (fun q=>if marked q && low q==i then some (Instr.lit ((List.range n).filter (member q))) else none) else []) := by
  let row := (v*M+j)*n
  let a:=(((s.assign 906 ((v*M:ℕ):ℤ)).assign 905 ((v*M+j:ℕ):ℤ)).assign 904 (row:ℤ)).assign 228 (row:ℤ)
  have first : Logical.Executes n m (chain litOpen) s a (23+6*M+6*n) := by
    apply evalLine_sound
    simp [litOpen,chain,evalLine,Operation.next,regularNext,a,row,Logical.State.assign,one,size,slots,vertex,word,
      show 0 ≤ (v:ℤ)*M+j by positivity]
    all_goals omega
  have D : LitData n row rep least matrix s marked low member := ⟨reps,minima,bitmap⟩
  let P := fun i (t:Logical.State)=>t.heap=s.heap ∧ t.closed=false ∧ t.reg 82=(t.output.length:ℤ) ∧
    t.output=s.output++(List.range i).flatMap (emitOwner n v who marked low member)
  have sz:=(first.preserves 64 (by decide)).trans size
  obtain ⟨t,k,ex,tm,res⟩ := Scene.GeometryTables.counted 229 912 64 n (95+n*(425+n*(171+6*n))) outerLit a P
    (by decide) (by decide) (by decide) (by decide) sz (by simp [P,a,Logical.State.assign,ready,count]) (by
      intro j u r v eq good;rcases eq with rfl|rfl <;> simpa [P,Logical.State.assign] using good) (by
      intro i hi u good fr idx
      obtain ⟨h,c,cn,o⟩:=good
      have eq (r : ℕ) (h₁ : writesReg r outerSweep=false) (h₂ : writesReg r (chain litOpen)=false) := (fr r h₁).trans (first.preserves r h₂)
      obtain ⟨z,l,run,bt,h',c',cn',out⟩:=outerLiteral n row v i owner rep least matrix m u who low marked member hi (D.keep h)
        ((eq 6 (by decide) (by decide)).trans one) ((fr 64 (by decide)).trans sz)
        ((fr 228 (by decide)).trans (by simp [a,Logical.State.assign])) idx
        ((eq 226 (by decide) (by decide)).trans vertex) ((eq 72 (by decide) (by decide)).trans ownAt)
        ((eq 77 (by decide) (by decide)).trans repAt) ((eq 78 (by decide) (by decide)).trans minAt)
        ((eq 80 (by decide) (by decide)).trans matAt) (by rw [h];exact ownership i hi) c cn
      refine ⟨z,l,run,bt,h'.trans h,c',cn',?_⟩
      rw [out,o];simp [List.range_succ,List.flatMap_append,List.append_assoc])
  obtain ⟨z,pre,zk⟩:=splitChain litOpen first
  refine ⟨t,_,pre.continue _ (.seq ex (.skip _)),?_,res⟩
  calc _  ≤  (23+6*M+6*n)+(9+n*((95+n*(425+n*(171+6*n)))+5))+2 := by omega
       _  ≤  _ := by ring_nf;omega

#print axioms solution
