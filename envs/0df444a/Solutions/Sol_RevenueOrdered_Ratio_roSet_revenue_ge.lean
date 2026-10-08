-- Prove2me | solution 1 for RevenueOrdered.Ratio.roSet_revenue_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:22:04.98873+00:00
-- url     : https://prove2.me/submissions/f4c67111-bf3f-4073-b466-cb8779035d4b

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Ratio_RevenueOrdered

set_option autoImplicit false

open RevenueOrdered.Ratio in
theorem solution {C : Type*} [Fintype C] [DecidableEq C]
    (P : C → Finset C → ℝ) (hP : RevenueOrdered.Ratio.IsRegular P) (r : C → ℝ) (hr : ∀ x, 0 < r x)
    (Sstar : Finset C) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ numVals r) :
    ∑ x ∈ Sstar ∩ roSet r i, P x Sstar * level r i ≤ revenue P r (roSet r i) := by
  set T := Sstar ∩ roSet r i with hT
  set S := roSet r i with hS
  have hTS : T ⊆ S := Finset.inter_subset_right
  have hTstar : T ⊆ Sstar := Finset.inter_subset_left
  -- level is nonneg? not needed: use r_i ≤ r x on S and positivity of r
  have hlev : ∀ x ∈ S, level r i ≤ r x := by
    intro x hx
    simpa [hS, roSet] using hx
  -- level r i is positive: it is a value of r (or 0); we only need 0 ≤ level r i
  have hlev0 : 0 ≤ level r i := by
    unfold level
    split_ifs with h
    · have hmem : sortedVals r ⟨i - 1, by omega⟩ ∈ revVals r := by
        unfold sortedVals
        exact Finset.orderEmbOfFin_mem _ _ _
      obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hmem
      rw [← hx]; exact (hr x).le
    · exact le_rfl
  -- step 1: P x Sstar ≤ P x T for x ∈ T
  have h1 : ∑ x ∈ T, P x Sstar * level r i ≤ ∑ x ∈ T, P x T * level r i := by
    apply Finset.sum_le_sum
    intro x hx
    exact mul_le_mul_of_nonneg_right (hP.mono T Sstar x hTstar hx) hlev0
  -- step 2: purchase probability monotone
  have h2 : ∑ x ∈ T, P x T ≤ ∑ x ∈ S, P x S := by
    have := hP.noPurchase_mono T S hTS
    unfold noPurchase at this
    linarith
  -- step 3: level ≤ r on S
  have h3 : ∑ x ∈ S, P x S * level r i ≤ ∑ x ∈ S, P x S * r x := by
    apply Finset.sum_le_sum
    intro x hx
    exact mul_le_mul_of_nonneg_left (hlev x hx) (hP.nonneg x S)
  calc ∑ x ∈ T, P x Sstar * level r i ≤ ∑ x ∈ T, P x T * level r i := h1
    _ = (∑ x ∈ T, P x T) * level r i := by rw [Finset.sum_mul]
    _ ≤ (∑ x ∈ S, P x S) * level r i := mul_le_mul_of_nonneg_right h2 hlev0
    _ = ∑ x ∈ S, P x S * level r i := by rw [Finset.sum_mul]
    _ ≤ ∑ x ∈ S, P x S * r x := h3
    _ = revenue P r S := rfl
