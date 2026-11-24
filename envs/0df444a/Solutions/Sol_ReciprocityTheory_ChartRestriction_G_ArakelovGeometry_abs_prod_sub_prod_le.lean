-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.abs_prod_sub_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:05.933864+00:00
-- url     : https://prove2.me/submissions/52650ca1-e551-4169-b69a-bac842acb463

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SupportSubsetMonoBox
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AbsProdSubProdSubLinLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_abs_prod_le_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_filter_lt_add_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_prod_sub_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {α : Type*} [LinearOrder α] (s : Finset α) (y ε : α → ℝ) {Y E : ℝ}
    (hY : 1 ≤ Y) (hE : 0 ≤ E) (hy : ∀ i ∈ s, |y i| ≤ Y) (hε : ∀ i ∈ s, |ε i| ≤ E) :
    |∏ i ∈ s, y i - ∏ i ∈ s, (y i - ε i)| ≤ s.card * E * (Y + E) ^ (s.card - 1) := by
  rw [prod_sub_eq_sum]
  have hYE : 1 ≤ Y + E := by linarith
  calc |∑ i ∈ s, ε i * (∏ j ∈ s with j < i, (y j - ε j)) * ∏ j ∈ s with i < j, y j|
      ≤ ∑ i ∈ s, |ε i * (∏ j ∈ s with j < i, (y j - ε j)) * ∏ j ∈ s with i < j, y j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, E * (Y + E) ^ (s.card - 1) := Finset.sum_le_sum fun i hi => ?_
    _ = s.card * E * (Y + E) ^ (s.card - 1) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [abs_mul, abs_mul]
  have h1 : |∏ j ∈ s with j < i, (y j - ε j)| ≤ (Y + E) ^ (s.filter (· < i)).card :=
    abs_prod_le_pow _ _ fun j hj => by
      have hj' := (Finset.mem_filter.mp hj).1
      exact (abs_sub _ _).trans (add_le_add (hy j hj') (hε j hj'))
  have h2 : |∏ j ∈ s with i < j, y j| ≤ (Y + E) ^ (s.filter (i < ·)).card :=
    abs_prod_le_pow _ _ fun j hj => (hy j (Finset.mem_filter.mp hj).1).trans (by linarith)
  have hc := card_filter_lt_add_gt s hi
  calc |ε i| * |∏ j ∈ s with j < i, (y j - ε j)| * |∏ j ∈ s with i < j, y j|
      ≤ E * (Y + E) ^ (s.filter (· < i)).card * (Y + E) ^ (s.filter (i < ·)).card := by
        gcongr
        exact hε i hi
    _ = E * (Y + E) ^ ((s.filter (· < i)).card + (s.filter (i < ·)).card) := by rw [pow_add]; ring
    _ ≤ E * (Y + E) ^ (s.card - 1) := by gcongr <;> first | exact hYE | omega
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
