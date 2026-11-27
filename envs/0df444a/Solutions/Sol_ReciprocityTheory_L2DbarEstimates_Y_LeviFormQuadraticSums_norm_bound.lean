-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums.norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:30:59.248891+00:00
-- url     : https://prove2.me/submissions/15a93899-0d58-4e23-a7ba-23fe31cac8fd

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeDA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeD
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LeviFormQuadraticSums_norm_sum_mul_sq_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums
variable {n d : ℕ} {p : V n → V d} {U : Set (V n)}
namespace ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums
theorem _root_.solution (c : ℝ) (hc : 0 < c) (x y : Fin d → ℂ) (P : V d) (hP : ∀ k, ‖x k‖ = ‖P k‖)
    (B : ℝ) (hB : B = ∑ k, ‖y k‖ ^ 2) :
    ‖∑ k, (c : ℂ)⁻¹ * (x k * y k)‖ ^ 2 ≤ (‖P‖ ^ 2 / c) * (c⁻¹ * B) := by
  rw [← Finset.mul_sum, norm_mul, mul_pow, EuclideanSpace.norm_sq_eq]
  have cs := norm_sum_mul_sq_le x y
  simp only [hP] at cs
  rw [← hB] at cs
  have hn : ‖(c : ℂ)⁻¹‖ = c⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hc.le]
  rw [hn]
  have e : (∑ k, ‖P k‖ ^ 2) / c * (c⁻¹ * B) = c⁻¹ ^ 2 * ((∑ k, ‖P k‖ ^ 2) * B) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left cs (sq_nonneg _)
end ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums
