-- Prove2me | solution 1 for TwoSidedPI.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:20:53.26003+00:00
-- url     : https://prove2.me/submissions/383a1899-9bd6-4d29-911a-b4b043442008

import Mathlib
import Definitions.Def_TwoSidedPI_OptB

open TwoSidedPI in
theorem solution {B : Type*} [Fintype B] [DecidableEq B] (M : Matroid B) (hE : M.E = Set.univ)
    (v : B → ℝ) (hv : ∀ k, 0 ≤ v k) (i : B) (AB : Finset B) (r : ℕ)
    (hi : i ∉ AB) (hind : M.Indep ↑(insert i AB)) (hcard : (insert i AB).card ≤ r) :
    optB M v AB r - optB M v (insert i AB) r ≥ optB M v AB r - optB M v AB (r - 1) := by
  classical
  have hmem : ∀ B' : Finset B, Disjoint B' (insert i AB) ∧ M.Indep ↑(B' ∪ insert i AB) ∧
      (B' ∪ insert i AB).card ≤ r →
      Disjoint B' AB ∧ M.Indep ↑(B' ∪ AB) ∧ (B' ∪ AB).card ≤ r - 1 := by
    rintro B' ⟨hd, hI, hc⟩
    have hiB' : i ∉ B' := fun h => Finset.disjoint_left.mp hd h (Finset.mem_insert_self i AB)
    have hiU : i ∉ B' ∪ AB := by
      rw [Finset.mem_union]; tauto
    refine ⟨Finset.disjoint_of_subset_right (Finset.subset_insert i AB) hd, ?_, ?_⟩
    · refine hI.subset (Finset.coe_subset.mpr (fun x hx => ?_))
      rw [Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (Finset.mem_insert_of_mem hx)
    · rw [Finset.union_insert, Finset.card_insert_of_notMem hiU] at hc
      omega
  have h0 : Disjoint (∅ : Finset B) AB ∧ M.Indep ↑((∅ : Finset B) ∪ AB) ∧
      ((∅ : Finset B) ∪ AB).card ≤ r - 1 := by
    have := hmem ∅ ⟨Finset.disjoint_empty_left _, by rw [Finset.empty_union]; exact hind,
      by rw [Finset.empty_union]; exact hcard⟩
    exact this
  have key : optB M v (insert i AB) r ≤ optB M v AB (r - 1) := by
    unfold optB
    dsimp only
    split_ifs with h1 h2 h2
    · refine Finset.sup'_le _ _ (fun B' hB' => ?_)
      refine Finset.le_sup' (fun B' => ∑ i ∈ B', v i) ?_
      rw [Finset.mem_filter] at hB' ⊢
      exact ⟨Finset.mem_univ _, hmem B' hB'.2⟩
    · exfalso
      obtain ⟨B', hB'⟩ := h1
      rw [Finset.mem_filter] at hB'
      exact h2 ⟨B', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem B' hB'.2⟩⟩
    · refine le_trans ?_ (Finset.le_sup' (fun B' : Finset B => ∑ i ∈ B', v i) (b := ∅) ?_)
      · simp
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, h0⟩
    · exact le_refl _
  linarith
