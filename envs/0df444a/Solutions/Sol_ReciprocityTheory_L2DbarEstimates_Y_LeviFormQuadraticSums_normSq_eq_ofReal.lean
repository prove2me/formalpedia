-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums.normSq_eq_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:40:06.882566+00:00
-- url     : https://prove2.me/submissions/d4efce54-cd07-433e-9058-de991137b476

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeDA

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
theorem _root_.solution {z : ℂ} : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.sq_norm]
end ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums
