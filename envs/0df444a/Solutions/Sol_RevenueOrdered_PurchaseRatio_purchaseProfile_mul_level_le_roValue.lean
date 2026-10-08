-- Prove2me | solution 1 for RevenueOrdered.PurchaseRatio.purchaseProfile_mul_level_le_roValue
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T12:05:51.888738+00:00
-- url     : https://prove2.me/submissions/256a3fda-8cea-43a3-8ff5-3a55b0f8077a

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_RevenueOrdered_Ratio_RevenueOrdered
import Definitions.Def_RevenueOrdered_PurchaseRatio_PurchaseProfile

set_option autoImplicit false

lemma c95d5b4f_level_pos {C : Type*} [Fintype C] (r : C → ℝ) (hr : ∀ x, 0 < r x)
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
lemma c95d5b4f_profile_le {C : Type*} [Fintype C]
    (P : C → Finset C → ℝ) (hP : RevenueOrdered.Ratio.IsRegular P) (r : C → ℝ)
    (S : Finset C) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ RevenueOrdered.Ratio.numVals r) :
    purchaseProfile P r S i ≤
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

open RevenueOrdered.PurchaseRatio in
theorem solution {C : Type*} [Fintype C] [Nonempty C]
    (P : C → Finset C → ℝ) (hP : RevenueOrdered.Ratio.IsRegular P) (r : C → ℝ) (hr : ∀ x, 0 < r x)
    (S : Finset C) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ RevenueOrdered.Ratio.numVals r) :
    purchaseProfile P r S i * RevenueOrdered.Ratio.level r i ≤ RevenueOrdered.Ratio.roValue P r := by
  have h1 := c95d5b4f_profile_le P hP r S i hi1 hik
  have hpos := c95d5b4f_level_pos r hr i hi1 hik
  have h2 : purchaseProfile P r S i * RevenueOrdered.Ratio.level r i ≤
      RevenueOrdered.Ratio.revenue P r (RevenueOrdered.Ratio.roSet r i) := by
    calc purchaseProfile P r S i * RevenueOrdered.Ratio.level r i
        ≤ (∑ x ∈ RevenueOrdered.Ratio.roSet r i, P x (RevenueOrdered.Ratio.roSet r i)) *
            RevenueOrdered.Ratio.level r i := mul_le_mul_of_nonneg_right h1 hpos.le
      _ = ∑ x ∈ RevenueOrdered.Ratio.roSet r i,
            P x (RevenueOrdered.Ratio.roSet r i) * RevenueOrdered.Ratio.level r i := Finset.sum_mul _ _ _
      _ ≤ RevenueOrdered.Ratio.revenue P r (RevenueOrdered.Ratio.roSet r i) := by
          unfold RevenueOrdered.Ratio.revenue
          apply Finset.sum_le_sum
          intro x hx
          apply mul_le_mul_of_nonneg_left _ (hP.nonneg x _)
          unfold RevenueOrdered.Ratio.roSet at hx
          exact (Finset.mem_filter.mp hx).2
  refine h2.trans ?_
  unfold RevenueOrdered.Ratio.roValue
  exact Finset.le_sup' (fun j => RevenueOrdered.Ratio.revenue P r (RevenueOrdered.Ratio.roSet r j))
    (Finset.mem_Icc.mpr ⟨hi1, hik⟩)
