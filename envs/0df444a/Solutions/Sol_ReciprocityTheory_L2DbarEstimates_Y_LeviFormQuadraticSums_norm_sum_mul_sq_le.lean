-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums.norm_sum_mul_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:40:09.49948+00:00
-- url     : https://prove2.me/submissions/d7defa53-3504-4a53-8665-62a30e73f8af

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeDA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums
theorem _root_.solution {d : ℕ} (x y : Fin d → ℂ) :
    ‖∑ k, x k * y k‖ ^ 2 ≤ (∑ k, ‖x k‖ ^ 2) * (∑ k, ‖y k‖ ^ 2) := by
  have h1 : ‖∑ k, x k * y k‖ ≤ ∑ k, ‖x k‖ * ‖y k‖ :=
    (norm_sum_le _ _).trans (le_of_eq (by simp))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖x k‖) (fun k => ‖y k‖)
  calc ‖∑ k, x k * y k‖ ^ 2 ≤ (∑ k, ‖x k‖ * ‖y k‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2
end ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums
