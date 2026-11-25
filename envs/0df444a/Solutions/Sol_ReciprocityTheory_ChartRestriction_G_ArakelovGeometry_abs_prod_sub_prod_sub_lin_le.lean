-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.abs_prod_sub_prod_sub_lin_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:42:05.122874+00:00
-- url     : https://prove2.me/submissions/c9429734-e5b7-4976-9bc2-5131744c2c31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SupportSubsetMonoBox
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AbsProdSubProdSubLinLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_abs_prod_le_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_filter_lt_add_gt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_prod_sub_eq_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_abs_prod_sub_prod_le

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
    |∏ i ∈ s, y i - ∏ i ∈ s, (y i - ε i) -
        ∑ i ∈ s, ε i * (∏ j ∈ s with j < i, y j) * ∏ j ∈ s with i < j, y j| ≤
      s.card * ((s.card - 1 : ℕ) : ℝ) * E ^ 2 * (Y + E) ^ (s.card - 2) := by
  rw [prod_sub_eq_sum, ← Finset.sum_sub_distrib]
  have hYE : 1 ≤ Y + E := by linarith
  calc |∑ i ∈ s, (ε i * (∏ j ∈ s with j < i, (y j - ε j)) * ∏ j ∈ s with i < j, y j -
          ε i * (∏ j ∈ s with j < i, y j) * ∏ j ∈ s with i < j, y j)|
      ≤ ∑ i ∈ s, |ε i * (∏ j ∈ s with j < i, (y j - ε j)) * ∏ j ∈ s with i < j, y j -
          ε i * (∏ j ∈ s with j < i, y j) * ∏ j ∈ s with i < j, y j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, ((s.card - 1 : ℕ) : ℝ) * E ^ 2 * (Y + E) ^ (s.card - 2) :=
        Finset.sum_le_sum fun i hi => ?_
    _ = s.card * ((s.card - 1 : ℕ) : ℝ) * E ^ 2 * (Y + E) ^ (s.card - 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [show ε i * (∏ j ∈ s with j < i, (y j - ε j)) * ∏ j ∈ s with i < j, y j -
      ε i * (∏ j ∈ s with j < i, y j) * ∏ j ∈ s with i < j, y j =
      -(ε i * (∏ j ∈ s with j < i, y j - ∏ j ∈ s with j < i, (y j - ε j)) *
        ∏ j ∈ s with i < j, y j) by ring, abs_neg, abs_mul, abs_mul]
  set a := (s.filter (· < i)).card
  set b := (s.filter (i < ·)).card
  have h1 := abs_prod_sub_prod_le (s.filter (· < i)) y ε hY hE
    (fun j hj => hy j (Finset.mem_filter.mp hj).1) (fun j hj => hε j (Finset.mem_filter.mp hj).1)
  have h2 : |∏ j ∈ s with i < j, y j| ≤ (Y + E) ^ b :=
    abs_prod_le_pow _ _ fun j hj => (hy j (Finset.mem_filter.mp hj).1).trans (by linarith)
  have hc := card_filter_lt_add_gt s hi
  have has : (a : ℝ) ≤ ((s.card - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_add_right a b).trans hc
  rcases Nat.eq_zero_or_pos a with ha | ha
  · have : (s.filter (· < i)) = ∅ := Finset.card_eq_zero.mp ha
    rw [this, Finset.prod_empty, Finset.prod_empty, sub_self, abs_zero, mul_zero, zero_mul]
    positivity
  calc |ε i| * |∏ j ∈ s with j < i, y j - ∏ j ∈ s with j < i, (y j - ε j)| * |∏ j ∈ s with i < j, y j|
      ≤ E * (a * E * (Y + E) ^ (a - 1)) * (Y + E) ^ b := by
        gcongr
        exact hε i hi
    _ = a * E ^ 2 * (Y + E) ^ (a - 1 + b) := by rw [pow_add]; ring
    _ ≤ ((s.card - 1 : ℕ) : ℝ) * E ^ 2 * (Y + E) ^ (s.card - 2) := by
        gcongr <;> first | exact hYE | omega | exact has
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
