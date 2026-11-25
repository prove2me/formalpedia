-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.first_distinct_row_scan
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-25T04:49:41.83457+00:00
-- url     : https://prove2.me/submissions/5f824b3a-ea0b-41c7-ab6c-4e20f6b57775

import Definitions.Def_StableMSR_VertexBlockRows
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_matrix_and_row_scans
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
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical

section
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option linter.all false
set_option maxRecDepth 35000
set_option maxHeartbeats 4100000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 35000
theorem source_loop {N:ℕ} {input:ℤ → ℤ} (ix last n cap:ℕ) (body:Program) (P:ℕ→State→Prop) (ne:ix≠last)
    (step:∀i<n,∀s:State,P i s → s.reg ix=(i:ℤ) → s.reg last=(n:ℤ)-1 →
      ∃t k,Executes N input body s t k ∧ k≤cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) (t.assign ix (t.reg ix+1)))
    (i rem:ℕ) (len:i+rem=n) (s:State) (start:P i s) (idx:s.reg ix=(i:ℤ)) (lim:s.reg last=(n:ℤ)-1) :
    ∃t k,Executes N input (.loop ix last (chain [body,.op (.regular (.inc ix))])) s t k ∧ k≤1+rem*(cap+5) ∧ P n t :=by
  induction rem generalizing i s with
  | zero=>
    have eq:i=n:=by omega
    exact ⟨s,1,.stop (by rw [idx,lim];omega),by omega,eq ▸ start⟩
  | succ r ih=>
    have lt:i<n:=by omega
    obtain ⟨u,k,ex,tim,idx',lim',next⟩:=step i lt s start idx lim
    let v:=u.assign ix (u.reg ix+1)
    have vi:v.reg ix=((i+1:ℕ):ℤ):=by simp [v,State.assign,idx',idx]
    have vl:v.reg last=(n:ℤ)-1:=by simp [v,State.assign,Ne.symm ne,lim',lim]
    obtain ⟨t,z,more,tm,out⟩:=ih (i+1) (by omega) v next vi vl
    have full:Executes N input (chain [body,.op (.regular (.inc ix))]) s v (1+k+(1+1+1)):=.seq ex (.seq (.op rfl) (.skip _))
    exact ⟨t,_,.more (by rw [idx,lim];omega) full more,by rw [Nat.succ_mul];omega,out⟩

def forSetup (ix last len:ℕ) (s:State) := let u:=s.assign ix 0; let v:=u.assign last (u.reg len);v.assign last (v.reg last-1)
theorem source_for {N:ℕ} {input:ℤ → ℤ} (ix last len n cap:ℕ) (body:Program) (P:ℕ→State→Prop)
    (ne:ix≠last) (dis:len≠ix) (s:State) (size:s.reg len=(n:ℤ))
    (start:P 0 (forSetup ix last len s))
    (step:∀i<n,∀s:State,P i s → s.reg ix=(i:ℤ) → s.reg last=(n:ℤ)-1 →
      ∃t k,Executes N input body s t k ∧ k≤cap ∧ t.reg ix=s.reg ix ∧ t.reg last=s.reg last ∧ P (i+1) (t.assign ix (t.reg ix+1))) :
    ∃t k,Executes N input (forCount ix last len body) s t k ∧ k≤9+n*(cap+5) ∧ P n t :=by
  let u:=forSetup ix last len s
  have fi:u.reg ix=0:=by simp [u,forSetup,State.assign,ne]
  have last':u.reg last=(n:ℤ)-1:=by simp [u,forSetup,State.assign,dis,size]
  obtain ⟨t,z,loop,tm,out⟩:=source_loop ix last n cap body P ne step 0 n (by omega) u start fi last'
  refine ⟨t,_,.seq (.op rfl) (.seq (.op rfl) (.seq (.op rfl) (.seq loop (.skip _)))),by omega,out⟩


end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
inductive PrefixRun (N:ℕ) (input:ℤ → ℤ) : List Program → State → State → ℕ → Prop where
  | nil (s:State) : PrefixRun N input [] s s 0
  | cons {p ps s u t a z} : Executes N input p s u a → PrefixRun N input ps u t z →
    PrefixRun N input (p::ps) s t (1+a+z)
theorem PrefixRun.continue {N input ps s t z} (h:PrefixRun N input ps s t z)
    (q:Program) {u k} (tail:Executes N input q t u k):
    Executes N input (ps.foldr Program.seq q) s u (z+k):=by
  induction h with
  | nil=>simpa using tail
  | cons run _ ih=>
    simpa [Nat.add_assoc] using Executes.seq run (ih tail)
theorem PrefixRun.finish {N input ps s t z} (h:PrefixRun N input ps s t z):
    Executes N input (chain ps) s t (z+1):=h.continue .skip (.skip t)
end Logical
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
def evalLine (n:ℕ) (m:ℤ → ℤ) : Program → State → Option (State×ℕ)
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
theorem evalLine_sound {n m} (p:Program) (s t:State) (k:ℕ) (ex:evalLine n m p s=some (t,k)):
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

def writesOp (j:ℕ) : Operation → Bool
  | .regular (.store _ _)|.save _ _ _=>false
  | .regular (.set d _)|.regular (.copy d _)|.regular (.add d _ _)|.regular (.sub d _ _)|
    .regular (.inc d)|.regular (.dec d)|.regular (.load d _)|.multiply d _ _|.divide _ d _ _|
    .fetch d _ _|.shift d _ _=>j==d
  | .alloc d _=>j==d || j==8
  | .output=>j==82
def writesReg (j:ℕ) : Program → Bool
  | .skip=>false | .op o=>writesOp j o | .seq p q|.cond _ _ p q=>writesReg j p || writesReg j q
  | .loop _ _ p=>writesReg j p
theorem op_preserves {n input s t k} (o:Operation) (j:ℕ) (frame:writesOp j o=false)
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
theorem Executes.preserves {n input p s t k} (ex:Executes n input p s t k) (j:ℕ) (off:writesReg j p=false):
    t.reg j=s.reg j:=by
  induction ex with
  | skip|stop=>rfl
  | op h=>exact op_preserves _ _ off h
  | seq _ _ ih jh=>obtain ⟨a,b⟩:=Bool.or_eq_false_iff.mp off;exact (jh b).trans (ih a)
  | yes _ _ ih=>exact ih (Bool.or_eq_false_iff.mp off).1
  | no _ _ ih=>exact ih (Bool.or_eq_false_iff.mp off).2
  | more _ _ _ ih jh=>exact (jh off).trans (ih off)
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
open scoped Classical
theorem splitChain {N input} (ps:List Program) {s t:State} {k:ℕ} (ex:Executes N input (chain ps) s t k) :
    ∃z,PrefixRun N input ps s t z ∧ k=z+1:=by
  induction ps generalizing s t k with
  | nil=>cases ex;exact ⟨0,.nil _,rfl⟩
  | cons p ps ih=>
    change Executes N input (.seq p (chain ps)) s t k at ex
    cases ex with
    | seq left right=>
      obtain ⟨z,e,h⟩:=ih right
      exact ⟨_,.cons left e,by omega⟩
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM



end
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical
set_option linter.all false
set_option maxRecDepth 35000
set_option maxHeartbeats 4100000
set_option autoImplicit false

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.GeometryTables
/-- Registers outside the write set retain the values with which the loop started. -/
lemma outside_for {ix last len r : ℕ} {body : Program}
    (off : writesReg r (forCount ix last len body) = false) :
    r ≠ ix ∧ r ≠ last ∧ writesReg r body = false := by
  simpa [forCount,chain,writesReg,writesOp,and_assoc,and_left_comm,and_comm] using off

lemma counted {n : ℕ} {m : ℤ → ℤ} (ix last len count cap : ℕ) (body : Program)
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
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows
private lemma rep_mem {n : ℕ} {W : Cluster n} {C : ℕ → Cluster n} {i : ℕ} :
    i ∈ representatives W C ↔
      (∃ p ∈ W, p.val = i) ∧ ∀ q ∈ W, q.val < i → C q.val ≠ C i := by
  simp only [representatives, Finset.mem_filter, Finset.mem_image]

private lemma first_of_seed {n : ℕ} {W : Cluster n} {C : ℕ → Cluster n} (p : Fin n) (hp : p ∈ W) :
    ∃ i ∈ representatives W C, i ≤ p.val ∧ C i = C p.val := by
  classical
  let S := (W.image Fin.val).filter (fun i => C i = C p.val)
  have hpS : p.val ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,rfl⟩
  let a := S.min' ⟨_,hpS⟩
  have ha : a ∈ S := Finset.min'_mem _ _
  obtain ⟨haW,haC⟩ := Finset.mem_filter.mp ha
  refine ⟨a,rep_mem.mpr ⟨Finset.mem_image.mp haW,?_⟩,Finset.min'_le _ _ hpS,haC⟩
  intro q hq lt eq
  have hqS : q.val ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨q,hq,rfl⟩,eq.trans haC⟩
  exact (Nat.not_le_of_lt lt) (Finset.min'_le _ _ hqS)

lemma least_earlier {n : ℕ} {W : Cluster n} {C : ℕ → Cluster n} (p : Fin n) (hp : p ∈ W) :
    p.val ∈ representatives W C ↔ ¬∃ i ∈ representatives W C, i < p.val ∧ C i = C p.val := by
  constructor
  · rintro current ⟨i,hi,lt,eq⟩
    obtain ⟨q,hq,rfl⟩ := (rep_mem.mp hi).1
    exact (rep_mem.mp current).2 q hq lt eq
  · intro none
    obtain ⟨i,hi,le,eq⟩ := first_of_seed (C:=C) p hp
    have same : i=p.val := by
      by_contra ne
      exact none ⟨i,hi,by omega,eq⟩
    simpa only [← same] using hi

private def dRead : List Program := [
  .op (.fetch 533 171 178),
  .op (.regular (.copy 532 533))
]
private def dAddr : List Program := [
  .op (.regular (.add 541 165 178)),
  .op (.multiply 540 541 64),
  .op (.regular (.add 538 80 540)),
  .op (.regular (.copy 148 176)),
  .op (.regular (.copy 149 538))
]
private def dResult : List Program := [
  .op (.regular (.copy 536 152)),
  .op (.regular (.copy 532 536))
]
private def dClear : List Program := [
  .op (.regular (.set 545 0)),
  .op (.regular (.copy 177 545))
]
private def dInit : List Program := [
  .op (.regular (.set 529 1)),
  .op (.regular (.copy 177 529))
]
private def dCompare := chain (dAddr ++ [src_equal_rows] ++ dResult)
private def dStep := chain (dRead ++ [.cond 6 532 dCompare .skip, .cond 6 532 (chain dClear) .skip])
private lemma dIdentify : checkRepresentative = chain (dInit ++ [forCount 178 531 173 dStep]) := by rfl

private lemma dCompare_run (n b mat p i : ℕ) (m : ℤ → ℤ) (s : State)
    (one : s.reg 6 = 1) (sz : s.reg 64 = (n:ℤ)) (base : s.reg 165 = (b:ℤ))
    (heapPtr : s.reg 80 = (mat:ℤ)) (ix : s.reg 178 = (i:ℤ))
    (ptr : s.reg 176 = ((mat+(b+p)*n:ℕ):ℤ)) :
    ∃ t k, Executes n m dCompare s t k ∧ k ≤ 65+156*n ∧
      (1 ≤ t.reg 532 ↔ ∀ q < n, s.heap (mat+(b+p)*n+q) = s.heap (mat+(b+i)*n+q)) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  have setup : ∃ a j, evalLine n m (chain dAddr) s = some (a,j) ∧ j ≤ 20+6*n ∧
      a.reg 148=((mat+(b+p)*n:ℕ):ℤ) ∧ a.reg 149=((mat+(b+i)*n:ℕ):ℤ) ∧
      a.heap=s.heap ∧ a.output=s.output ∧ a.closed=s.closed := by
    simp [dAddr,chain,evalLine,Operation.next,regularNext,State.assign,one,sz,base,ix,heapPtr,ptr,
      show 0 ≤ (b:ℤ)+i by positivity] <;> omega
  obtain ⟨a,j,ev,jt,left,right,ah,ao,ac⟩ := setup
  have setupRun := evalLine_sound _ _ _ _ ev
  obtain ⟨v,l,cmp,lt,eq,bits,hm,om,cm⟩ := matrix_and_row_scans.2.2 n _ _ m a
    ((setupRun.preserves 6 (by decide)).trans one) ((setupRun.preserves 64 (by decide)).trans sz) left right
  let t := (v.assign 536 (v.reg 152)).assign 532 (v.reg 152)
  have finish : Executes n m (chain dResult) v t 5 := by
    apply evalLine_sound
    simp [dResult,chain,evalLine,Operation.next,regularNext,t,State.assign]
  obtain ⟨z,pr,hz⟩ := splitChain dAddr setupRun
  have tail := Executes.seq cmp finish
  have run := pr.continue _ tail
  refine ⟨t,_,run,by omega,?_,hm.trans ah,om.trans ao,cm.trans ac⟩
  change 1 ≤ v.reg 152 ↔ _
  rw [←ah,←eq]
  rcases bits with b|b <;> simp [b]

private lemma dStep_run (n b mat mark p i : ℕ) (m : ℤ → ℤ) (s : State)
    (one : s.reg 6 = 1) (sz : s.reg 64=(n:ℤ)) (base : s.reg 165=(b:ℤ))
    (heapPtr : s.reg 80=(mat:ℤ)) (mask : s.reg 171=(mark:ℤ)) (ix : s.reg 178=(i:ℤ))
    (ptr : s.reg 176=((mat+(b+p)*n:ℕ):ℤ)) :
    let hit := 1 ≤ s.heap (mark+i) ∧ ∀ q < n, s.heap (mat+(b+p)*n+q)=s.heap (mat+(b+i)*n+q)
    ∃ t k, Executes n m dStep s t k ∧ k ≤ 210+156*n ∧
      t.reg 177 = (if hit then 0 else s.reg 177) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  dsimp only
  let hit := 1 ≤ s.heap (mark+i) ∧ ∀ q < n, s.heap (mat+(b+p)*n+q)=s.heap (mat+(b+i)*n+q)
  let a := (s.assign 533 (s.heap (mark+i))).assign 532 (s.heap (mark+i))
  have read : Executes n m (chain dRead) s a 68 := by
    apply evalLine_sound
    simp [dRead,chain,evalLine,Operation.next,regularNext,State.assign,a,mask,ix,
      show 0 ≤ (mark:ℤ)+i by omega,show ((mark:ℤ)+i).toNat=mark+i by omega]
  have oneA : a.reg 6=1 := (read.preserves 6 (by decide)).trans one
  have readA : a.reg 532=s.heap (mark+i) := by simp [a,State.assign]
  have test : ∃ z j, Executes n m (.cond 6 532 dCompare .skip) a z j ∧ j ≤ 66+156*n ∧
      (1 ≤ z.reg 532 ↔ hit) ∧ z.heap=s.heap ∧ z.output=s.output ∧ z.closed=s.closed := by
    by_cases sel : 1 ≤ s.heap (mark+i)
    · obtain ⟨z,j,ex,tm,rel,hm,om,cm⟩ := dCompare_run n b mat p i m a oneA
        ((read.preserves 64 (by decide)).trans sz) ((read.preserves 165 (by decide)).trans base)
        ((read.preserves 80 (by decide)).trans heapPtr) ((read.preserves 178 (by decide)).trans ix)
        ((read.preserves 176 (by decide)).trans ptr)
      refine ⟨z,_,.yes (by rwa [oneA,readA]) ex,by omega,?_,hm,om,cm⟩
      simpa [hit,sel,a,State.assign] using rel
    · exact ⟨a,_,.no (by rwa [oneA,readA]) (.skip _),by omega,by simp [readA,hit,sel],rfl,rfl,rfl⟩
  obtain ⟨z,j,ex,tm,cond,hm,om,cm⟩ := test
  have oneZ := (ex.preserves 6 (by decide)).trans oneA
  have prev := (ex.preserves 177 (by decide)).trans (read.preserves 177 (by decide))
  have finish : ∃ t l, Executes n m (.cond 6 532 (chain dClear) .skip) z t l ∧ l ≤ 6 ∧
      t.reg 177=(if hit then 0 else s.reg 177) ∧ t.heap=z.heap ∧ t.output=z.output ∧ t.closed=z.closed := by
    by_cases yes : hit
    · let u := (z.assign 545 0).assign 177 0
      have clear : Executes n m (chain dClear) z u 5 := by
        apply evalLine_sound
        simp [dClear,chain,evalLine,Operation.next,regularNext,State.assign,u]
      exact ⟨u,_,.yes (oneZ ▸ cond.mpr yes) clear,by omega,by simp [u,State.assign,yes],rfl,rfl,rfl⟩
    · exact ⟨z,_,.no (by rw [oneZ]; exact fun h => yes (cond.mp h)) (.skip _),by omega,by simpa [yes] using prev,rfl,rfl,rfl⟩
  obtain ⟨t,l,last,lt,flag,th,tout,tc⟩ := finish
  obtain ⟨j0,pr,hj⟩ := splitChain dRead read
  exact ⟨t,_,pr.continue _ (.seq ex (.seq last (.skip _))),by omega,flag,th.trans hm,tout.trans om,tc.trans cm⟩

lemma duplicate_scan
    (n b matrix mark : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (W : Cluster n) (C : ℕ → Cluster n) (p : Fin n) (hp : p ∈ W)
    (one : s.reg 6 = 1) (size : s.reg 64 = (n : ℤ)) (base : s.reg 165 = (b : ℤ))
    (mat : s.reg 80 = (matrix : ℤ)) (mask : s.reg 171 = (mark : ℤ))
    (seed : s.reg 173 = (p.val : ℤ)) (row : s.reg 176 = ((matrix+(b+p.val)*n : ℕ) : ℤ))
    (selected : ∀ i < p.val, 1 ≤ s.heap (mark+i) ↔ i ∈ representatives W C)
    (rows : ∀ i, i = p.val ∨ (i < p.val ∧ i ∈ representatives W C) →
      ∀ q : Fin n, s.heap (matrix+(b+i)*n+q.val) = if q ∈ C i then 1 else 0) :
    ∃ t k, Logical.Executes n m checkRepresentative s t k ∧ k ≤ 600*(n+1)^2 ∧
      t.reg 177 = (if p.val ∈ representatives W C then 1 else 0) ∧
      t.heap = s.heap ∧ t.output = s.output ∧ t.closed = s.closed
    := by
  classical
  let R := representatives W C
  let ok (j : ℕ) := ¬∃ i ∈ R, i < j ∧ C i=C p.val
  have next (j : ℕ) : ok (j+1) ↔ ok j ∧ ¬(j ∈ R ∧ C j=C p.val) := by
    constructor
    · intro h
      exact ⟨fun ⟨i,hi,lt,e⟩ => h ⟨i,hi,by omega,e⟩,fun ⟨hj,e⟩ => h ⟨j,hj,by omega,e⟩⟩
    · rintro ⟨h,ne⟩ ⟨i,hi,lt,e⟩
      by_cases eq : i=j
      · exact ne (eq ▸ And.intro hi e)
      · exact h ⟨i,hi,by omega,e⟩
  have agree (i : ℕ) (lt : i < p.val) (selectedI : i ∈ R) :
      (∀ q < n,s.heap (matrix+(b+p.val)*n+q)=s.heap (matrix+(b+i)*n+q)) ↔ C i=C p.val := by
    have a := rows _ (.inl rfl)
    have z := rows i (.inr ⟨lt,selectedI⟩)
    constructor
    · intro h
      ext q
      have same := h q.val q.isLt
      rw [a q,z q] at same
      by_cases hpq : q ∈ C p.val <;> by_cases hiq : q ∈ C i <;> simp_all
    · intro e j hj
      rw [a ⟨j,hj⟩,z ⟨j,hj⟩,e]
  let a := (s.assign 529 1).assign 177 1
  have init : Executes n m (chain dInit) s a 5 := by
    apply evalLine_sound
    simp [dInit,chain,evalLine,Operation.next,regularNext,State.assign,a]
  let P (j : ℕ) (z : State) := z.reg 177=(if ok j then 1 else 0) ∧
    z.heap=s.heap ∧ z.output=s.output ∧ z.closed=s.closed
  have start : P 0 a := by simp [P,a,State.assign,ok]
  obtain ⟨t,k,loop,tm,flag,hm,om,cm⟩ := GeometryTables.counted (n:=n) (m:=m)
    178 531 173 p.val (210+156*n) dStep a P (by decide) (by decide) (by decide) (by decide)
    ((init.preserves 173 (by decide)).trans seed) start (by
      intro j z r v cases prev
      rcases cases with rfl|rfl <;> simpa [P,State.assign] using prev) (by
      intro i lt z good fr idx
      obtain ⟨fz,hz,oz,cz⟩ := good
      obtain ⟨v,l,ex,tl,flag,hm,om,cm⟩ := dStep_run n b matrix mark p.val i m z
        ((fr 6 (by decide)).trans ((init.preserves 6 (by decide)).trans one))
        ((fr 64 (by decide)).trans ((init.preserves 64 (by decide)).trans size))
        ((fr 165 (by decide)).trans ((init.preserves 165 (by decide)).trans base))
        ((fr 80 (by decide)).trans ((init.preserves 80 (by decide)).trans mat))
        ((fr 171 (by decide)).trans ((init.preserves 171 (by decide)).trans mask)) idx
        ((fr 176 (by decide)).trans ((init.preserves 176 (by decide)).trans row))
      have test : (1 ≤ z.heap (mark+i) ∧ ∀ q < n, z.heap (matrix+(b+p.val)*n+q)=z.heap (matrix+(b+i)*n+q)) ↔
          (i ∈ R ∧ C i=C p.val) := by
        rw [hz,selected i lt]
        exact and_congr_right (fun hi => agree i lt hi)
      refine ⟨v,l,ex,tl,?_,hm.trans hz,om.trans oz,cm.trans cz⟩
      rw [flag,if_congr test rfl rfl,fz]
      simp only [next i]
      by_cases on : i ∈ R ∧ C i=C p.val <;> simp [on])
  obtain ⟨aCost,pr,eq⟩ := splitChain dInit init
  have charge : 9+p.val*((210+156*n)+5) ≤ 9+n*((210+156*n)+5) :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ p.isLt.le) _
  rw [dIdentify]
  refine ⟨t,_,pr.continue _ (.seq loop (.skip _)),?_,?_,hm,om,cm⟩
  · ring_nf at tm charge ⊢ <;> omega
  · simpa only [ok,R,←least_earlier (C:=C) p hp] using flag

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows
theorem solution
    (n b matrix mark : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (W : Cluster n) (C : ℕ → Cluster n) (p : Fin n) (hp : p ∈ W)
    (one : s.reg 6 = 1) (size : s.reg 64 = (n : ℤ)) (base : s.reg 165 = (b : ℤ))
    (mat : s.reg 80 = (matrix : ℤ)) (mask : s.reg 171 = (mark : ℤ))
    (seed : s.reg 173 = (p.val : ℤ)) (row : s.reg 176 = ((matrix+(b+p.val)*n : ℕ) : ℤ))
    (selected : ∀ i < p.val, 1 ≤ s.heap (mark+i) ↔ i ∈ representatives W C)
    (rows : ∀ i, i = p.val ∨ (i < p.val ∧ i ∈ representatives W C) →
      ∀ q : Fin n, s.heap (matrix+(b+i)*n+q.val) = if q ∈ C i then 1 else 0) :
    ∃ t k, Logical.Executes n m checkRepresentative s t k ∧ k ≤ 600*(n+1)^2 ∧
      t.reg 177 = (if p.val ∈ representatives W C then 1 else 0) ∧
      t.heap = s.heap ∧ t.output = s.output ∧ t.closed = s.closed
 := StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.duplicate_scan n b matrix mark m s W C p hp one size base mat mask seed row selected rows
