-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums.q_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:31:06.329565+00:00
-- url     : https://prove2.me/submissions/6367a2ae-15e1-442d-8aa6-8dec3d99e328

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeDA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_LeviFormQuadraticSums_normSq_eq_ofReal
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
variable {d : ℕ} (p : V n → V d) (U : Set (V n)) (c : ℝ)
namespace ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums
theorem _root_.solution : (fun x => ((‖p x‖ ^ 2 / c : ℝ) : ℂ)) =
    fun x => ∑ k, (c : ℂ)⁻¹ * (p x k * conj (p x k : ℂ)) := by
  funext x
  simp only [normSq_eq_ofReal]
  rw [EuclideanSpace.norm_sq_eq]
  push_cast
  rw [div_eq_inv_mul, Finset.mul_sum]
end ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums
