-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.commit_representative_metadata
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-25T04:56:51.01338+00:00
-- url     : https://prove2.me/submissions/12dfed55-1456-4637-b4ae-b3495346d90b

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
private def cMarks : List Program := [
  .op (.regular (.set 550 1)),
  .op (.save 171 173 550),
  .op (.regular (.add 553 165 173)),
  .op (.regular (.set 556 1)),
  .op (.save 77 553 556),
  .op (.regular (.copy 144 176))
]
private def cDecision : List Program := [
  .op (.regular (.copy 557 147)),
  .op (.regular (.copy 179 557)),
  .cond 179 64 (.cond 64 179 (.op (.regular (.set 559 1))) (.op (.regular (.set 559 0)))) (.op (.regular (.set 559 0)))
]
private def cEmpty : List Program := [
  .op (.regular (.set 562 0)),
  .op (.regular (.copy 172 562))
]
private def cMin : List Program := [
  .op (.regular (.add 565 165 173)),
  .op (.save 78 565 179)
]
private def cTouchBody : List Program := [
  .op (.fetch 572 176 174),
  .op (.regular (.copy 571 572)),
  .cond 6 571 (chain [.op (.fetch 576 72 174),
                    .cond 576 162 (.cond 162 576 (.op (.regular (.set 575 1))) (.op (.regular (.set 575 0)))) (.op (.regular (.set 575 0))),
                    .op (.regular (.copy 571 575))]) (.skip),
  .cond 6 571 (chain [.op (.regular (.add 582 165 173)),
                    .op (.regular (.set 585 1)),
                    .op (.save 79 582 585)]) (.skip)
]
private def cTouch := forCount 174 570 64 (chain cTouchBody)
private def cNon := chain (cMin ++ [cTouch])
private def cLast := Program.cond 6 559 (chain cEmpty) cNon
private def cWork := chain (cMarks ++ [src_first] ++ cDecision ++ [cLast])
private lemma cSource : instruction seedWork 8 = .cond 6 177 cWork .skip := by rfl

private lemma first_bitmap {n : ℕ} (C : Cluster n) (s : State) (row : ℕ)
    (bits : ∀ q : Fin n, 1 ≤ s.heap (row+q.val) ↔ q∈C) :
    ((List.range n).filter (fun i => decide (1 ≤ s.heap (row+i)))).headD n =
      if ne : C.Nonempty then (C.min' ne).val else n := by
  classical
  let L := (List.range n).filter (fun i => decide (1 ≤ s.heap (row+i)))
  have member (j : ℕ) : j ∈ L ↔ ∃ q ∈ C, q.val=j := by
    simp only [L,List.mem_filter,List.mem_range,decide_eq_true_eq]
    constructor
    · rintro ⟨lt,h⟩; exact ⟨⟨j,lt⟩,(bits ⟨j,lt⟩).mp h,rfl⟩
    · rintro ⟨q,hq,rfl⟩; exact ⟨q.isLt,(bits q).mpr hq⟩
  have sorted : L.Pairwise (· < ·) := List.pairwise_lt_range.filter _
  change L.headD n=_
  cases eq : L with
  | nil =>
    have empty : ¬C.Nonempty := by
      rintro ⟨q,hq⟩
      have h := (member q.val).mpr ⟨q,hq,rfl⟩
      simp [eq] at h
    simp [empty]
  | cons a tail =>
    obtain ⟨q,hq,hval⟩ := (member a).mp (by simp [eq])
    have ne : C.Nonempty := ⟨q,hq⟩
    let small := C.min' ne
    have sm : small ∈ C := C.min'_mem ne
    have smle : small ≤ q := C.min'_le q hq
    have among := (member small.val).mpr ⟨small,sm,rfl⟩
    rw [eq,List.mem_cons] at among
    rw [eq,List.pairwise_cons] at sorted
    have other : a ≤ small.val := by
      rcases among with same|ht
      · exact same.ge
      · exact (sorted.1 _ ht).le
    have rev : small.val ≤ q.val := smle
    simp only [List.headD_cons,dif_pos ne]
    change a=small.val
    omega

private noncomputable def markTouch (f : ℕ → ℤ) (a : ℕ) (yes : Prop) : ℕ → ℤ :=
  if yes then Function.update f a 1 else f

private lemma touch_step (n base touch seed vertex row own i : ℕ) (m : ℤ → ℤ) (s : State)
    (one : s.reg 6=1) (ix : s.reg 174=(i:ℤ)) (r : s.reg 176=(row:ℤ)) (o : s.reg 72=(own:ℤ))
    (v : s.reg 162=(vertex:ℤ)) (b : s.reg 165=(base:ℤ)) (p : s.reg 173=(seed:ℤ)) (toff : s.reg 79=(touch:ℤ)) :
    ∃ t k, Executes n m (chain cTouchBody) s t k ∧ k ≤ 240 ∧
      t.heap=markTouch s.heap (touch+(base+seed)) (1 ≤ s.heap (row+i) ∧ s.heap (own+i)=(vertex:ℤ)) ∧
      t.output=s.output ∧ t.closed=s.closed := by
  have ev : ∃ t k, evalLine n m (chain cTouchBody) s=some (t,k) ∧ k ≤ 240 ∧
      t.heap=markTouch s.heap (touch+(base+seed)) (1 ≤ s.heap (row+i) ∧ s.heap (own+i)=(vertex:ℤ)) ∧
      t.output=s.output ∧ t.closed=s.closed := by
    have eqv : (s.heap (own+i)=(vertex:ℤ)) ↔ s.heap (own+i) ≤ (vertex:ℤ) ∧ (vertex:ℤ) ≤ s.heap (own+i) := by omega
    by_cases on : 1 ≤ s.heap (row+i) <;> by_cases lo : s.heap (own+i) ≤ (vertex:ℤ) <;>
      by_cases hi : (vertex:ℤ) ≤ s.heap (own+i) <;>
      simp [cTouchBody,markTouch,chain,evalLine,Operation.next,regularNext,State.assign,State.save,one,ix,r,o,v,b,p,toff,
        show 0 ≤ (row:ℤ)+i by omega,show ((row:ℤ)+i).toNat=row+i by omega,
        show 0 ≤ (own:ℤ)+i by omega,show ((own:ℤ)+i).toNat=own+i by omega,
        show 0 ≤ (touch:ℤ)+((base:ℤ)+seed) by omega,show ((touch:ℤ)+((base:ℤ)+seed)).toNat=touch+(base+seed) by omega,
        eqv,on,lo,hi] <;> omega
  obtain ⟨t,k,e,tm,w⟩ := ev
  exact ⟨t,k,evalLine_sound _ _ _ _ e,tm,w⟩

private lemma touch_loop (n base touch seed vertex row own : ℕ) (m : ℤ → ℤ) (s : State)
    (C : Cluster n) (owner : Fin n → Fin n) (one : s.reg 6=1) (sz : s.reg 64=(n:ℤ))
    (r : s.reg 176=(row:ℤ)) (o : s.reg 72=(own:ℤ)) (v : s.reg 162=(vertex:ℤ))
    (b : s.reg 165=(base:ℤ)) (p : s.reg 173=(seed:ℤ)) (toff : s.reg 79=(touch:ℤ))
    (bits : ∀ q : Fin n, 1 ≤ s.heap (row+q.val) ↔ q∈C)
    (owners : ∀ q : Fin n, s.heap (own+q.val)=((owner q).val:ℤ))
    (dis : ∀ q : Fin n,touch+(base+seed) ≠ row+q.val ∧ touch+(base+seed) ≠ own+q.val) :
    ∃ t k, Executes n m cTouch s t k ∧ k ≤ 9+245*n ∧
      t.heap=markTouch s.heap (touch+(base+seed)) (∃ q∈C,(owner q).val=vertex) ∧
      t.output=s.output ∧ t.closed=s.closed := by
  classical
  let seen (j : ℕ) := ∃ q ∈ C, q.val < j ∧ (owner q).val=vertex
  let ptr := touch+(base+seed)
  let P (j : ℕ) (z : State) := z.heap=markTouch s.heap ptr (seen j) ∧ z.output=s.output ∧ z.closed=s.closed
  obtain ⟨t,k,ex,tm,hm,om,cm⟩ := GeometryTables.counted (n:=n) (m:=m)
    174 570 64 n 240 (chain cTouchBody) s P (by decide) (by decide) (by decide) (by decide) sz
    (by simp [P,seen,markTouch]) (by intro j z a v cases prev;rcases cases with rfl|rfl <;> simpa [P,State.assign] using prev) (by
      intro i hi z good fr ix
      obtain ⟨heap,out,closed⟩ := good
      let q : Fin n := ⟨i,hi⟩
      have keep (a : ℕ) (off : a ≠ ptr) : z.heap a=s.heap a := by
        rw [heap]; by_cases old : seen i <;> simp [markTouch,old,off]
      have test : (1 ≤ z.heap (row+i) ∧ z.heap (own+i)=(vertex:ℤ)) ↔ (q∈C ∧ (owner q).val=vertex) := by
        rw [keep _ (Ne.symm (dis q).1),keep _ (Ne.symm (dis q).2),bits q,owners q]
        simp
      have succ : seen (i+1) ↔ (q∈C ∧ (owner q).val=vertex) ∨ seen i := by
        constructor
        · rintro ⟨a,ha,lt,owna⟩
          by_cases eq : a.val=i
          · have eq' : a=q := Fin.ext eq
            exact .inl (eq' ▸ And.intro ha owna)
          · exact .inr ⟨a,ha,by omega,owna⟩
        · rintro (⟨hq,ownq⟩|⟨a,ha,lt,owna⟩)
          · exact ⟨q,hq,by dsimp [q];omega,ownq⟩
          · exact ⟨a,ha,by omega,owna⟩
      obtain ⟨t,l,step,bound,th,tout,tc⟩ := touch_step n base touch seed vertex row own i m z
        ((fr 6 (by decide)).trans one) ix ((fr 176 (by decide)).trans r) ((fr 72 (by decide)).trans o)
        ((fr 162 (by decide)).trans v) ((fr 165 (by decide)).trans b) ((fr 173 (by decide)).trans p)
        ((fr 79 (by decide)).trans toff)
      refine ⟨t,l,step,bound,?_,tout.trans out,tc.trans closed⟩
      rw [th]
      simp only [markTouch,test,succ]
      by_cases old : seen i <;> by_cases yes : q∈C ∧ (owner q).val=vertex <;>
        simp [heap,markTouch,old,yes,ptr,Function.update_idem])
  have final : seen n ↔ ∃ q∈C,(owner q).val=vertex := by
    constructor
    · rintro ⟨q,h,_,e⟩;exact ⟨q,h,e⟩
    · rintro ⟨q,h,e⟩;exact ⟨q,h,q.isLt,e⟩
  exact ⟨t,k,ex,by omega,by by_cases yn : ∃ q∈C,(owner q).val=vertex <;> simpa [markTouch,final,yn,ptr] using hm,om,cm⟩

private lemma make_marks (n base mark rep seed row : ℕ) (m : ℤ → ℤ) (s : State)
    (b : s.reg 165=(base:ℤ)) (p : s.reg 173=(seed:ℤ)) (loc : s.reg 171=(mark:ℤ))
    (dest : s.reg 77=(rep:ℤ)) (r : s.reg 176=(row:ℤ)) :
    ∃ t k, Executes n m (chain cMarks) s t k ∧ k ≤ 145 ∧ t.reg 144=(row:ℤ) ∧
      t.heap=Function.update (Function.update s.heap (mark+seed) 1) (rep+(base+seed)) 1 ∧
      t.output=s.output ∧ t.closed=s.closed := by
  have ev : ∃ t k,evalLine n m (chain cMarks) s=some (t,k) ∧ k ≤ 145 ∧ t.reg 144=(row:ℤ) ∧
      t.heap=Function.update (Function.update s.heap (mark+seed) 1) (rep+(base+seed)) 1 ∧
      t.output=s.output ∧ t.closed=s.closed := by
    simp [cMarks,chain,evalLine,Operation.next,regularNext,State.assign,State.save,b,p,loc,dest,r,
      show 0 ≤ (mark:ℤ)+seed by omega,show ((mark:ℤ)+seed).toNat=mark+seed by omega,
      show 0 ≤ (rep:ℤ)+((base:ℤ)+seed) by omega,show ((rep:ℤ)+((base:ℤ)+seed)).toNat=rep+(base+seed) by omega]
  obtain ⟨t,k,e,tm,w⟩ := ev
  exact ⟨t,k,evalLine_sound _ _ _ _ e,tm,w⟩

private lemma first_test (n v : ℕ) (m : ℤ → ℤ) (s : State) (sz : s.reg 64=(n:ℤ)) (f : s.reg 147=(v:ℤ)) :
    ∃ t k, Executes n m (chain cDecision) s t k ∧ k ≤ 10 ∧ t.reg 179=(v:ℤ) ∧
      t.reg 559=(if v=n then 1 else 0) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  have ev : ∃ t k, evalLine n m (chain cDecision) s=some (t,k) ∧ k ≤ 10 ∧ t.reg 179=(v:ℤ) ∧
      t.reg 559=(if v=n then 1 else 0) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
    rcases lt_trichotomy v n with lt|same|gt
    · simp [cDecision,chain,evalLine,Operation.next,regularNext,State.assign,sz,f,lt.le,not_le.mpr lt,ne_of_lt lt]
    · simp [cDecision,chain,evalLine,Operation.next,regularNext,State.assign,sz,f,same]
    · simp [cDecision,chain,evalLine,Operation.next,regularNext,State.assign,sz,f,not_le.mpr gt,ne_of_gt gt]
  obtain ⟨t,k,e,tm,w⟩ := ev
  exact ⟨t,k,evalLine_sound _ _ _ _ e,tm,w⟩

private lemma store_minimum (n base minimum seed f : ℕ) (m : ℤ → ℤ) (s : State)
    (b : s.reg 165=(base:ℤ)) (p : s.reg 173=(seed:ℤ)) (atMin : s.reg 78=(minimum:ℤ)) (atF : s.reg 179=(f:ℤ)) :
    ∃ t k, Executes n m (chain cMin) s t k ∧ k ≤ 70 ∧
      t.heap=Function.update s.heap (minimum+(base+seed)) (f:ℤ) ∧ t.output=s.output ∧ t.closed=s.closed := by
  have ev : ∃ t k, evalLine n m (chain cMin) s=some (t,k) ∧ k ≤ 70 ∧
      t.heap=Function.update s.heap (minimum+(base+seed)) (f:ℤ) ∧ t.output=s.output ∧ t.closed=s.closed := by
    simp [cMin,chain,evalLine,Operation.next,regularNext,State.assign,State.save,b,p,atMin,atF,
      show 0 ≤ (minimum:ℤ)+((base:ℤ)+seed) by omega,
      show ((minimum:ℤ)+((base:ℤ)+seed)).toNat=minimum+(base+seed) by omega]
  obtain ⟨t,k,e,tm,w⟩ := ev
  exact ⟨t,k,evalLine_sound _ _ _ _ e,tm,w⟩

lemma commit_metadata
    (n base mark rep minimum touch row own seed vertex : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (C : Cluster n) (owner : Fin n → Fin n) (selected : s.reg 177 = 1)
    (one : s.reg 6 = 1) (size : s.reg 64 = (n:ℤ)) (seedAt : s.reg 173 = (seed:ℤ))
    (baseAt : s.reg 165 = (base:ℤ)) (markAt : s.reg 171 = (mark:ℤ)) (repAt : s.reg 77 = (rep:ℤ))
    (minAt : s.reg 78 = (minimum:ℤ)) (touchAt : s.reg 79 = (touch:ℤ)) (rowAt : s.reg 176 = (row:ℤ))
    (ownerAt : s.reg 72 = (own:ℤ)) (vertexAt : s.reg 162 = (vertex:ℤ))
    (bits : ∀ q : Fin n, 1 ≤ s.heap (row+q.val) ↔ q∈C)
    (owners : ∀ q : Fin n, s.heap (own+q.val) = ((owner q).val:ℤ))
    (disjoint : ∀ a ∈ [mark+seed,rep+(base+seed),minimum+(base+seed),touch+(base+seed)],
      ∀ q : Fin n, a ≠ row+q.val ∧ a ≠ own+q.val) :
    let key := base+seed
    let marked := Function.update (Function.update s.heap (mark+seed) 1) (rep+key) 1
    let withMin := if ne : C.Nonempty then Function.update marked (minimum+key) (((C.min' ne).val):ℤ) else marked
    ∃ t k, Logical.Executes n m (instruction seedWork 8) s t k ∧ k ≤ 700*(n+1) ∧
      t.reg 172 = (if C.Nonempty then s.reg 172 else 0) ∧
      t.heap = (if ∃ q ∈ C, (owner q).val=vertex then Function.update withMin (touch+key) 1 else withMin) ∧
      t.output=s.output ∧ t.closed=s.closed
    := by
  classical
  dsimp only
  let key := base+seed
  let marked := Function.update (Function.update s.heap (mark+seed) 1) (rep+key) 1
  let f := if ne : C.Nonempty then (C.min' ne).val else n
  let result := if ne : C.Nonempty then Function.update marked (minimum+key) (((C.min' ne).val):ℤ) else marked
  let anyOwned := ∃ q ∈ C, (owner q).val=vertex
  obtain ⟨a,i,init,it,a144,ah,ao,ac⟩ := make_marks n base mark rep seed row m s baseAt seedAt markAt repAt rowAt
  change a.heap=marked at ah
  have retain (q : Fin n) : marked (row+q.val)=s.heap (row+q.val) ∧ marked (own+q.val)=s.heap (own+q.val) := by
    obtain ⟨x,y⟩ := disjoint (mark+seed) (by simp) q
    obtain ⟨x',y'⟩ := disjoint (rep+key) (by simp [key]) q
    simp [marked,Ne.symm x,Ne.symm x',Ne.symm y,Ne.symm y']
  obtain ⟨v,j,find,jt,first,vh,vo,vc⟩ := matrix_and_row_scans.2.1 n row m a
    ((init.preserves 6 (by decide)).trans one) ((init.preserves 64 (by decide)).trans size) a144
  have fv : v.reg 147=(f:ℤ) := first.trans (congrArg (fun i : ℕ => (i:ℤ)) (first_bitmap C a row
    (fun q => by rw [ah,(retain q).1]; exact bits q)))
  obtain ⟨z,l,decideRun,lt,z179,z559,zh,zo,zc⟩ := first_test n f m v
    ((find.preserves 64 (by decide)).trans ((init.preserves 64 (by decide)).trans size)) fv
  have safe (r : ℕ) (pre : writesReg r (chain cMarks)=false) (mid : writesReg r src_first=false)
      (last : writesReg r (chain cDecision)=false) : z.reg r=s.reg r :=
    (decideRun.preserves _ last).trans ((find.preserves _ mid).trans (init.preserves _ pre))
  have oneZ := (safe 6 (by decide) (by decide) (by decide)).trans one
  have heapZ := zh.trans (vh.trans ah)
  have branch : ∃ t e, Executes n m cLast z t e ∧ e ≤ 90+245*n ∧
      t.reg 172=(if C.Nonempty then s.reg 172 else 0) ∧ t.heap=markTouch result (touch+key) anyOwned ∧
      t.output=z.output ∧ t.closed=z.closed := by
    by_cases ne : C.Nonempty
    · have less : f<n := by simpa [f,ne] using (C.min' ne).isLt
      have gate : ¬z.reg 6 ≤ z.reg 559 := by rw [oneZ,z559,if_neg (ne_of_lt less)]; decide
      obtain ⟨u,k,mn,kt,uh,uo,uc⟩ := store_minimum n base minimum seed f m z
        ((safe 165 (by decide) (by decide) (by decide)).trans baseAt)
        ((safe 173 (by decide) (by decide) (by decide)).trans seedAt)
        ((safe 78 (by decide) (by decide) (by decide)).trans minAt) z179
      have writes : u.heap=result := by simp [uh,heapZ,result,ne,f,key]
      have readback (q : Fin n) : u.heap (row+q.val)=s.heap (row+q.val) ∧ u.heap (own+q.val)=s.heap (own+q.val) := by
        obtain ⟨x,y⟩ := disjoint (minimum+key) (by simp [key]) q
        rw [uh,heapZ]
        change Function.update marked (minimum+key) (f:ℤ) (row+q.val)=_ ∧ Function.update marked (minimum+key) (f:ℤ) (own+q.val)=_
        simpa only [Function.update_of_ne (Ne.symm x),Function.update_of_ne (Ne.symm y)] using retain q
      have fr (r : ℕ) (a : writesReg r (chain cMarks)=false) (b : writesReg r src_first=false)
          (c : writesReg r (chain cDecision)=false) (d : writesReg r (chain cMin)=false) : u.reg r=s.reg r :=
        (mn.preserves _ d).trans (safe r a b c)
      obtain ⟨t,steps,ex,tm,th,tout,tc⟩ := touch_loop n base touch seed vertex row own m u C owner
        ((mn.preserves 6 (by decide)).trans oneZ) ((fr 64 (by decide) (by decide) (by decide) (by decide)).trans size)
        ((fr 176 (by decide) (by decide) (by decide) (by decide)).trans rowAt)
        ((fr 72 (by decide) (by decide) (by decide) (by decide)).trans ownerAt)
        ((fr 162 (by decide) (by decide) (by decide) (by decide)).trans vertexAt)
        ((fr 165 (by decide) (by decide) (by decide) (by decide)).trans baseAt)
        ((fr 173 (by decide) (by decide) (by decide) (by decide)).trans seedAt)
        ((fr 79 (by decide) (by decide) (by decide) (by decide)).trans touchAt)
        (fun q => by rw [(readback q).1]; exact bits q) (fun q => (readback q).2.trans (owners q))
        (disjoint _ (by simp))
      obtain ⟨k',prMin,add⟩ := splitChain cMin mn
      have non : Executes n m cNon z t (k'+(1+steps+1)) := prMin.continue _ (.seq ex (.skip _))
      refine ⟨t,_,.no gate non,by omega,?_,?_,tout.trans uo,tc.trans uc⟩
      · simpa only [if_pos ne] using (ex.preserves 172 (by decide)).trans (fr 172 (by decide) (by decide) (by decide) (by decide))
      · simpa [writes,anyOwned,key] using th
    · have sentinel : f=n := by simp [f,ne]
      let t := (z.assign 562 0).assign 172 0
      have clear : Executes n m (chain cEmpty) z t 5 := by
        apply evalLine_sound
        simp [cEmpty,chain,evalLine,Operation.next,regularNext,t,State.assign]
      have none : ¬anyOwned := by rintro ⟨q,hq,_⟩;exact ne ⟨q,hq⟩
      refine ⟨t,_,.yes (by simp [oneZ,z559,sentinel]) clear,by omega,?_,?_,rfl,rfl⟩
      · simp [t,State.assign,ne]
      · simpa [t,State.assign,markTouch,none,result,ne] using heapZ
  obtain ⟨t,c,br,ct,flag,th,tout,tc⟩ := branch
  obtain ⟨i',p1,eq1⟩ := splitChain cMarks init
  obtain ⟨l',p2,eq2⟩ := splitChain cDecision decideRun
  have rem := p2.continue _ (Executes.seq br (.skip _))
  have whole := p1.continue _ (Executes.seq find rem)
  rw [cSource]
  refine ⟨t,_,Executes.yes (by rw [one,selected]) whole,by omega,flag,?_,tout.trans (zo.trans (vo.trans ao)),tc.trans (zc.trans (vc.trans ac))⟩
  by_cases yes : ∃ q ∈ C, (owner q).val=vertex <;> by_cases ne : C.Nonempty <;>
    simpa [markTouch,anyOwned,result,marked,key,yes,ne] using th

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows
theorem solution
    (n base mark rep minimum touch row own seed vertex : ℕ) (m : ℤ → ℤ) (s : Logical.State)
    (C : Cluster n) (owner : Fin n → Fin n) (selected : s.reg 177 = 1)
    (one : s.reg 6 = 1) (size : s.reg 64 = (n:ℤ)) (seedAt : s.reg 173 = (seed:ℤ))
    (baseAt : s.reg 165 = (base:ℤ)) (markAt : s.reg 171 = (mark:ℤ)) (repAt : s.reg 77 = (rep:ℤ))
    (minAt : s.reg 78 = (minimum:ℤ)) (touchAt : s.reg 79 = (touch:ℤ)) (rowAt : s.reg 176 = (row:ℤ))
    (ownerAt : s.reg 72 = (own:ℤ)) (vertexAt : s.reg 162 = (vertex:ℤ))
    (bits : ∀ q : Fin n, 1 ≤ s.heap (row+q.val) ↔ q∈C)
    (owners : ∀ q : Fin n, s.heap (own+q.val) = ((owner q).val:ℤ))
    (disjoint : ∀ a ∈ [mark+seed,rep+(base+seed),minimum+(base+seed),touch+(base+seed)],
      ∀ q : Fin n, a ≠ row+q.val ∧ a ≠ own+q.val) :
    let key := base+seed
    let marked := Function.update (Function.update s.heap (mark+seed) 1) (rep+key) 1
    let withMin := if ne : C.Nonempty then Function.update marked (minimum+key) (((C.min' ne).val):ℤ) else marked
    ∃ t k, Logical.Executes n m (instruction seedWork 8) s t k ∧ k ≤ 700*(n+1) ∧
      t.reg 172 = (if C.Nonempty then s.reg 172 else 0) ∧
      t.heap = (if ∃ q ∈ C, (owner q).val=vertex then Function.update withMin (touch+key) 1 else withMin) ∧
      t.output=s.output ∧ t.closed=s.closed
 := StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.BlockRows.commit_metadata n base mark rep minimum touch row own seed vertex m s C owner selected one size seedAt baseAt markAt repAt minAt touchAt rowAt ownerAt vertexAt bits owners disjoint
