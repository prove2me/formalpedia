-- Prove2me | solution 1 for OnlineCRS.Knapsack.big_selectable_condition
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:52:23.396794+00:00
-- url     : https://prove2.me/submissions/79c17e5b-588f-4562-91a4-6a7565df9114

import Mathlib
import Definitions.Def_OnlineCRS_Knapsack_Model

set_option autoImplicit false
open OnlineCRS.Knapsack

theorem solution {α : Type} [Fintype α] [DecidableEq α]
    (s : α → ℝ) (hs : ∀ e, 0 ≤ s e ∧ s e ≤ 1)
    (A : Finset α) (e : α) (he : e ∈ bigElements s)
    (hload : ∑ f ∈ ((A ∩ bigElements s).erase e), s f ≤ 1 - s e) :
    OnlineCRS.Matroid.Selectable (bigFamily s) A e := by
  intro I hIA hI
  unfold bigFamily at hI ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI ⊢
  obtain ⟨hIbig, hIfeas⟩ := hI
  refine ⟨?_, ?_⟩
  · intro f hf
    rw [Finset.mem_insert] at hf
    rcases hf with rfl | hf
    · exact he
    · exact hIbig hf
  · unfold knapsackFeasible at hIfeas ⊢
    by_cases heI : e ∈ I
    · rw [Finset.insert_eq_of_mem heI]; exact hIfeas
    · rw [Finset.sum_insert heI]
      have hsub : I ⊆ (A ∩ bigElements s).erase e := by
        intro f hf
        rw [Finset.mem_erase, Finset.mem_inter]
        exact ⟨fun h => heI (h ▸ hf), hIA hf, hIbig hf⟩
      have : ∑ f ∈ I, s f ≤ ∑ f ∈ (A ∩ bigElements s).erase e, s f :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun f _ _ => (hs f).1)
      linarith

