-- Prove2me | solution 1 for RevenueOrdered.PurchaseRatio.purchaseProfile_le_purchase_prob
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:18:28.43017+00:00
-- url     : https://prove2.me/submissions/13842420-0f19-4cec-9b65-2ea096bc1611

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Ratio_RevenueOrdered
import Definitions.Def_RevenueOrdered_PurchaseRatio_PurchaseProfile

set_option autoImplicit false

lemma d9e70560_level_pos {C : Type*} [Fintype C] (r : C → ℝ) (hr : ∀ x, 0 < r x)
    (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ RevenueOrdered.Ratio.numVals r) :
    0 < RevenueOrdered.Ratio.level r i := by
  unfold RevenueOrdered.Ratio.level
  rw [dif_pos ⟨hi1, hik⟩]
  have hmem : RevenueOrdered.Ratio.sortedVals r ⟨i - 1, by omega⟩ ∈
      RevenueOrdered.Ratio.revVals r := by
    unfold RevenueOrdered.Ratio.sortedVals
    exact Finset.orderEmbOfFin_mem _ _ _
  unfold RevenueOrdered.Ratio.revVals at hmem
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hmem
  rw [← hx]
  exact hr x

open RevenueOrdered.PurchaseRatio in
theorem solution {C : Type*} [Fintype C]
    (P : C → Finset C → ℝ) (hP : RevenueOrdered.Ratio.IsRegular P) (r : C → ℝ) (hr : ∀ x, 0 < r x)
    (S : Finset C) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ RevenueOrdered.Ratio.numVals r) :
    purchaseProfile P r S i ≤ ∑ x ∈ RevenueOrdered.Ratio.roSet r i, P x (RevenueOrdered.Ratio.roSet r i) ∧
      purchaseProfile P r S i * RevenueOrdered.Ratio.level r i ≤ ∑ x ∈ RevenueOrdered.Ratio.roSet r i, P x (RevenueOrdered.Ratio.roSet r i) * RevenueOrdered.Ratio.level r i := by
  have h1 : purchaseProfile P r S i ≤
      ∑ x ∈ RevenueOrdered.Ratio.roSet r i, P x (RevenueOrdered.Ratio.roSet r i) := by
    unfold purchaseProfile
    rw [if_pos ⟨hi1, hik⟩]
    set T := S.filter (fun x => RevenueOrdered.Ratio.level r i ≤ r x) with hT
    have hTS : T ⊆ S := Finset.filter_subset _ _
    have hTR : T ⊆ RevenueOrdered.Ratio.roSet r i := by
      intro x hx
      unfold RevenueOrdered.Ratio.roSet
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Finset.mem_filter.mp hx).2
    have hstep1 : ∑ x ∈ T, P x S ≤ ∑ x ∈ T, P x T :=
      Finset.sum_le_sum (fun x hx => hP.mono T S x hTS hx)
    have hstep2 := hP.noPurchase_mono T (RevenueOrdered.Ratio.roSet r i) hTR
    unfold RevenueOrdered.Ratio.noPurchase at hstep2
    linarith
  refine ⟨h1, ?_⟩
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right h1 (le_of_lt (d9e70560_level_pos r hr i hi1 hik))
