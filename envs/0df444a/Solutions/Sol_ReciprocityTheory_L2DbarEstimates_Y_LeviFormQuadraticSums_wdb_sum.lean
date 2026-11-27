-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums.wdb_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:31:10.897674+00:00
-- url     : https://prove2.me/submissions/51a46643-14f0-4997-bd91-21ad29939acd

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
theorem _root_.solution {ι : Type*} (s : Finset ι) {g : ι → V n → ℂ} {y : V n}
    (hg : ∀ i ∈ s, DifferentiableAt ℝ (g i) y) (j : Fin n) :
    wdb n j (fun w => ∑ i ∈ s, g i w) y = ∑ i ∈ s, wdb n j (g i) y := by
  simp only [wdb, fderiv_fun_sum hg, FunLike.coe_sum, Finset.sum_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]
end ReciprocityTheory.L2DbarEstimates.Y.LeviFormQuadraticSums
