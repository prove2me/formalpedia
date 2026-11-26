-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.check_selected_block_pair
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-26T03:11:31.414962+00:00
-- url     : https://prove2.me/submissions/4bc2d58d-b419-4ae4-85e2-25ae8e42b554

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_CutTraversal_compare_two_block_bitmaps
import Definitions.Def_StableMSR_VertexBlockRows
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


private def memBit {n : ℕ} (C : Cluster n) (i : ℕ) : Bool :=
  if h:i<n then decide ((⟨i,h⟩ : Fin n)∈C) else false
private lemma memBit_at {n : ℕ} (C : Cluster n) (i : Fin n) : memBit C i.val=decide (i∈C) := by
  simp [memBit,i.isLt]
private lemma overlap_iff {n : ℕ} (C D : Cluster n) :
    ((List.range n).any (fun j=>memBit C j && memBit D j))=true ↔ ¬Disjoint C D := by
  rw [List.any_eq_true,Finset.not_disjoint_iff]
  constructor
  · rintro ⟨i,hi,h⟩; have hi:=List.mem_range.mp hi
    exact ⟨⟨i,hi⟩,by simpa [memBit,hi] using h⟩
  · rintro ⟨p,hC,hD⟩
    exact ⟨p.val,List.mem_range.mpr p.isLt,by simp [memBit_at,hC,hD]⟩
private lemma equal_iff {n : ℕ} (C D : Cluster n) :
    ((List.range n).all (fun j=>memBit C j == memBit D j))=true ↔ C=D := by
  rw [List.all_eq_true];constructor
  · intro eq;ext p
    simpa [memBit_at] using eq p.val (List.mem_range.mpr p.isLt)
  · rintro rfl;simp
private def cmpStart : List Program := [.op (.regular (.add 830 208 212)),.op (.multiply 829 830 64),
  .op (.regular (.add 827 80 829)),.op (.regular (.copy 213 827)),.op (.regular (.set 834 0)),
  .op (.regular (.copy 214 834)),.op (.regular (.set 835 1)),.op (.regular (.copy 215 835))]
private def cmpFinish := chain [.op (.regular (.copy 854 214)),
  .cond 6 854 (chain [.cond 6 215 (.op (.regular (.set 856 0))) (.op (.regular (.set 856 1))),
    .op (.regular (.copy 854 856))]) .skip,
  .cond 6 854 (chain [.op (.regular (.set 858 0)),.op (.regular (.copy 209 858))]) .skip]
private lemma finishCmp (n : ℕ) (m : ℤ→ℤ) (s : State) (a b : Bool) (one : s.reg 6=1)
  (overlap : s.reg 214=if a then 1 else 0) (equal : s.reg 215=if b then 1 else 0) :
  ∃t k,Executes n m cmpFinish s t k ∧ k≤30 ∧
    t.reg 209=(if a && !b then 0 else s.reg 209) ∧ t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  let res := (evalLine n m cmpFinish s).getD (s,0)
  refine ⟨res.1,res.2,evalLine_sound _ _ _ _ ?_,?_,?_,?_,?_,?_⟩ <;>
    cases a <;> cases b <;> simp only [Bool.false_eq_true,reduceIte,if_false,if_true] at overlap equal <;>
    simp [res,cmpFinish,chain,evalLine,Operation.next,regularNext,State.assign,one,overlap,equal]

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open Scene.CutTraversal
theorem solution (n R j L matrix : ℕ) (m : ℤ → ℤ) (s : Logical.State) (C D : Cluster n)
    (one : s.reg 6=1) (size : s.reg 64=(n:ℤ))
    (left : s.reg 211=(L:ℤ)) (base : s.reg 208=(R:ℤ)) (index : s.reg 212=(j:ℤ)) (mat : s.reg 80=(matrix:ℤ))
    (bitsL : ∀p : Fin n,s.heap (L+p.val)=if p∈C then 1 else 0)
    (bitsR : ∀p : Fin n,s.heap (matrix+((R+j)*n+p.val))=if p∈D then 1 else 0) :
    ∃t k, Logical.Executes n m (Scene.BlockRows.insideBranch (Scene.BlockRows.instruction (Scene.BlockRows.countedBody (Scene.BlockRows.instruction (Scene.BlockRows.insideBranch (Scene.BlockRows.instruction (Scene.BlockRows.countedBody (Scene.BlockRows.instruction src_fits 10)) 4)) 4)) 4)) s t k ∧ k≤100+340*n ∧
      t.reg 209=(if Disjoint C D ∨ C=D then s.reg 209 else 0) ∧
      t.heap=s.heap ∧ t.output=s.output ∧ t.closed=s.closed := by
  let ptr := matrix+((R+j)*n)
  let u := (((((((s.assign 830 ((R+j:ℕ):ℤ)).assign 829 (((R+j)*n:ℕ):ℤ)).assign 827 (ptr:ℤ)).assign 213 (ptr:ℤ)).assign 834 0).assign 214 0).assign 835 1).assign 215 1
  have first : Logical.Executes n m (chain cmpStart) s u (24+6*n) := by
    apply evalLine_sound
    simp [cmpStart,chain,evalLine,Operation.next,regularNext,u,ptr,Logical.State.assign,one,size,base,index,mat,show 0≤(R:ℤ)+j by omega]
    all_goals omega
  have l := (first.preserves 211 (by decide)).trans left
  obtain ⟨v,k,run,time,x,y,heap,out,cl⟩ := compare_two_block_bitmaps n L ptr m u (memBit C) (memBit D)
    ((first.preserves 6 (by decide)).trans one) ((first.preserves 64 (by decide)).trans size)
    l (by simp [u,Logical.State.assign]) (by simp [u,Logical.State.assign]) (by simp [u,Logical.State.assign])
    (by intro q h;simpa [memBit,h,u,Logical.State.assign] using bitsL ⟨q,h⟩)
    (by intro q h;simpa [memBit,h,u,Logical.State.assign,ptr,Nat.add_assoc] using bitsR ⟨q,h⟩)
  obtain ⟨w,jcost,finish,timer,flag,hw,ow,cw⟩ := finishCmp n m v _ _ ((run.preserves 6 (by decide)).trans ((first.preserves 6 (by decide)).trans one)) x y
  obtain ⟨k0,pre,eq⟩:=splitChain cmpStart first
  refine ⟨w,_,pre.continue _ (.seq run finish),by omega,?_,hw.trans heap,ow.trans out,cw.trans cl⟩
  have r209 := (run.preserves 209 (by decide)).trans (first.preserves 209 (by decide))
  rw [flag,r209]
  cases ho : (List.range n).any (fun j=>memBit C j && memBit D j) <;>
    cases he : (List.range n).all (fun j=>memBit C j == memBit D j) <;>
    have hd := overlap_iff C D <;> have hc := equal_iff C D <;>
    rw [ho] at hd <;> rw [he] at hc <;> simp only [Bool.false_eq_true,not_false_eq_true,not_iff_self,
      false_iff,true_iff,not_not] at hd hc <;> simp [hd,hc]

#print axioms solution
