-- Prove2me | solution 1 for SubmodSparsify.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T17:01:23.741354+00:00
-- url     : https://prove2.me/submissions/c9690fc3-931d-4c85-ad8f-a28bf379b5b8

import Definitions.Def_SubmodSparsify_blockMinCut
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
open SubmodSparsify NonmonotoneSubmod.Shared
namespace Submod1327
variable {α : Type} [Fintype α] [DecidableEq α]

theorem cut_le (f : Finset α → ℝ) {A B T : Finset α} (hA : A ⊆ T) (hB : Disjoint T B) :
    blockMinCut f A B ≤ f T := by
  let g := fun x : {T : Finset α // A ⊆ T ∧ Disjoint T B} => f x.val
  exact ciInf_le (Set.finite_range g).bddBelow (⟨T,hA,hB⟩ : {T : Finset α // A ⊆ T ∧ Disjoint T B})

theorem attained (f : Finset α → ℝ) {A B : Finset α} (h : Disjoint A B) :
    ∃ T, A ⊆ T ∧ Disjoint T B ∧ f T = blockMinCut f A B := by
  let I := {T : Finset α // A ⊆ T ∧ Disjoint T B}
  have : Nonempty I := ⟨⟨A, Finset.Subset.rfl,h⟩⟩
  obtain ⟨T,hT⟩ := exists_eq_ciInf_of_finite (f := fun T : I => f T.val)
  exact ⟨T.val,T.property.1,T.property.2,hT⟩

theorem mono_cut (f : Finset α → ℝ) {A A' B B' : Finset α}
    (ha : A ⊆ A') (hb : B ⊆ B') (hd : Disjoint A' B') :
    blockMinCut f A B ≤ blockMinCut f A' B' := by
  obtain ⟨T,hT,hdT,he⟩ := attained f hd
  rw [← he]
  exact cut_le f (ha.trans hT) (hdT.mono_right hb)

end Submod1327
open Submod1327

theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (_hf0 : ∀ S, 0 ≤ f S)
    (hf : Submodular f) :
    (∀ A B B' : Finset (Fin n), Disjoint A B' → B ⊆ B' →
      blockMinCut f A B ≤ blockMinCut f A B') ∧
    (∀ A B B' : Finset (Fin n), Disjoint A B → Disjoint A B' →
      blockMinCut f A (B ∪ B') + blockMinCut f A (B ∩ B') ≤
        blockMinCut f A B + blockMinCut f A B') ∧
    (∀ B A A' : Finset (Fin n), Disjoint A' B → A ⊆ A' →
      blockMinCut f A B ≤ blockMinCut f A' B) ∧
    (∀ B A A' : Finset (Fin n), Disjoint A B → Disjoint A' B →
      blockMinCut f (A ∪ A') B + blockMinCut f (A ∩ A') B ≤
        blockMinCut f A B + blockMinCut f A' B) := by
  refine ⟨fun A B B' hd h => mono_cut f Finset.Subset.rfl h hd, ?_,
    fun B A A' hd h => mono_cut f h Finset.Subset.rfl hd, ?_⟩
  · intro A B B' h1 h2
    obtain ⟨T,hs,ht,he1⟩ := attained f h1
    obtain ⟨U,hu,hv,he2⟩ := attained f h2
    rw [← he1,← he2]
    rw [Finset.disjoint_left] at ht hv
    have hI : Disjoint (T ∩ U) (B ∪ B') := Finset.disjoint_left.mpr (by
      intro x hx hy
      rcases Finset.mem_union.mp hy with h | h
      · exact ht (Finset.mem_inter.mp hx).1 h
      · exact hv (Finset.mem_inter.mp hx).2 h)
    have hU : Disjoint (T ∪ U) (B ∩ B') := Finset.disjoint_left.mpr (by
      intro x hx hy
      rcases Finset.mem_union.mp hx with h | h
      · exact ht h (Finset.mem_inter.mp hy).1
      · exact hv h (Finset.mem_inter.mp hy).2)
    have hi := cut_le f (Finset.subset_inter hs hu) hI
    have hh := cut_le f (hs.trans (Finset.subset_union_left : T ⊆ T ∪ U)) hU
    linarith [hf T U]
  · intro B A A' h1 h2
    obtain ⟨T,hs,ht,he1⟩ := attained f h1
    obtain ⟨U,hu,hv,he2⟩ := attained f h2
    rw [← he1,← he2]
    have hh := cut_le f (Finset.union_subset_union hs hu) (Finset.disjoint_union_left.mpr ⟨ht,hv⟩)
    have hi := cut_le f (Finset.inter_subset_inter hs hu) (ht.mono_left (Finset.inter_subset_left (s₂ := U)))
    linarith [hf T U]
#print axioms solution
