-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal.child_boundary_after_deleting_vertex
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-26T03:48:53.058917+00:00
-- url     : https://prove2.me/submissions/a0cc543d-de3d-4b82-a701-136909882325

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

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open SingleCircuit TightLanguage
private abbrev Seen := Finset ℕ
private def rounds {A:Type} (f:A→A) (s:A) : ℕ→A
  | 0=>s | k+1=>f (rounds f s k)
private theorem rounds_shift {A:Type} (f:A→A) (s:A) (k:ℕ) : rounds f s (k+1)=rounds f (f s) k:=by
  induction k with | zero=>rfl | succ k ih=>change f (rounds f s (k+1))=f (rounds f (f s) k);rw [ih]
private theorem constant_rounds {A:Type} {f:A→A} {s:A} (h:f s=s) (k:ℕ) : rounds f s k=s:=by
  induction k with | zero=>rfl | succ k ih=>simp [rounds,ih,h]

private theorem fixed_after (f:Seen→Seen) (U:Seen) (ext:∀s,s⊆U → s⊆f s) (cap:∀s,s⊆U → f s⊆U)
    (k:ℕ) (s:Seen) (hs:s⊆U) (enough:U.card ≤ s.card+k) : f (rounds f s k)=rounds f s k:=by
  induction k generalizing s with
  | zero=>
    have eq:s=U:=Finset.eq_of_subset_of_card_le hs (by omega)
    exact Finset.Subset.antisymm ((cap s hs).trans eq.symm.subset) (ext s hs)
  | succ k ih=>
    by_cases fix:f s=s
    · rw [constant_rounds fix];exact fix
    have lt:s.card<(f s).card:=by
      by_contra! le
      exact fix (Finset.eq_of_subset_of_card_le (ext s hs) le).symm
    rw [rounds_shift]
    exact ih (f s) (cap s hs) (by omega)

private def advance (e:ℕ→ℕ→Bool) (U s:Seen) : Seen:=
  U.filter (fun u=>u∈s ∨ ∃z∈s,e z u=true)
@[simp] private theorem mem_advance (e:ℕ→ℕ→Bool) (U s:Seen) (u:ℕ) :
  u∈advance e U s ↔ u∈U ∧ (u∈s ∨ ∃z∈s,e z u=true):=by classical simp [advance]

private def passList (e:ℕ→ℕ→Bool) (us seen:List ℕ):=us.filter fun u=>seen.contains u || seen.any (fun z=>e z u)
private theorem list_advance (e:ℕ→ℕ→Bool) (us seen:List ℕ) :
    (passList e us seen).toFinset=advance e us.toFinset seen.toFinset:=by
  classical ext u;simp [passList]
private theorem ref_rounds (d:Instance) (us:List ℕ) (v k:ℕ) :
    ((List.range k).foldl (fun seen _=>passList d.edge us seen) [v]).toFinset =
      rounds (advance d.edge us.toFinset) {v} k:=by
  induction k with
  | zero=>simp [rounds]
  | succ k ih=>rw [List.range_succ,List.foldl_append];simp [rounds,list_advance,ih]
private lemma fixedPiece (d : Instance) (U : List ℕ) (seed : ℕ) (initial:seed∈U) (cap:U.toFinset.card≤d.n) :
    let C:=pieceAt d U seed
    C.toFinset⊆U.toFinset ∧ ∀p∈U,∀q∈C,d.edge q p=true → p∈C := by
  classical
  let f:=advance d.edge U.toFinset
  have ext (s:Seen) (hs:s⊆U.toFinset) : s⊆f s := by
    intro p hp;exact (mem_advance ..).mpr ⟨hs hp,.inl hp⟩
  have lim (s:Seen) : f s⊆U.toFinset := fun _ hp=>((mem_advance ..).mp hp).1
  have sub : ({seed}:Seen)⊆U.toFinset := by simpa using initial
  let X:=rounds f {seed} d.n
  have fixed : f X=X := fixed_after f U.toFinset ext (fun s _=>lim s) d.n {seed} sub (by simpa using (show U.toFinset.card≤1+d.n by omega))
  have id : (pieceAt d U seed).toFinset=X := ref_rounds d U seed d.n
  refine ⟨by rw [id,←fixed];exact lim _,?_⟩
  intro p hp q hq e
  have inside : q∈X := id ▸ List.mem_toFinset.mpr hq
  have hit : p∈f X := (mem_advance ..).mpr ⟨List.mem_toFinset.mpr hp,.inr ⟨q,inside,e⟩⟩
  apply List.mem_toFinset.mp;rw [id,←fixed];exact hit

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.CutTraversal
open Scene.CutTraversal TightLanguage SingleCircuit
theorem solution (d : SingleCircuit.Instance) (parent : List ℕ) (v child : ℕ)
    (bounded : parent.toFinset.card ≤ d.n) (seed : child∈parent.erase v) :
    let C:=TightLanguage.pieceAt d (parent.erase v) child
    ∀p∈TightLanguage.rimOf d C,p=v ∨ p∈TightLanguage.rimOf d parent := by
  let U:=parent.erase v
  let C:=pieceAt d U child
  have sub : U.toFinset⊆parent.toFinset := by
    intro p hp;exact List.mem_toFinset.mpr (List.mem_of_mem_erase (List.mem_toFinset.mp hp))
  have enough:= (Finset.card_le_card sub).trans bounded
  obtain ⟨within,closed⟩:=fixedPiece d U child seed enough
  dsimp only;intro p hp;change p∈rimOf d C at hp
  obtain ⟨active,rest⟩:=List.mem_filter.mp hp
  obtain ⟨away,q,inC,edge⟩ : p∉C ∧ ∃q∈C,d.edge q p=true := by simpa [List.any_eq_true] using rest
  have inParent : q∈parent := List.mem_toFinset.mp (sub (within (List.mem_toFinset.mpr inC)))
  by_cases h:p=v
  · exact .inl h
  · right;apply List.mem_filter.mpr;refine ⟨active,?_⟩
    have no : p∉parent := by
      intro yes;have inside : p∈U := (List.mem_erase_of_ne h).2 yes
      exact away (closed p inside q inC edge)
    simp only [Bool.and_eq_true,Bool.not_eq_true',List.any_eq_true]
    exact ⟨by simpa using no,q,inParent,edge⟩

#print axioms solution
