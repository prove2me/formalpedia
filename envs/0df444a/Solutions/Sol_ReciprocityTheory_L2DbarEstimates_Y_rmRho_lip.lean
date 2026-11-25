-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.rmRho_lip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:57:28.779201+00:00
-- url     : https://prove2.me/submissions/341f7034-c234-4311-9e80-46dfb28d5f84

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rmRho_hasDerivAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_rmRho_deriv
import Theorems.Thm_P2M_ReciprocityTheory_L2DbarEstimates_Y_abs_rmRho__le_1a70138217c8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (a b : ℝ) : |rmRho a - rmRho b| ≤ |a - b| := by
  have hL : LipschitzWith 1 rmRho := by
    refine lipschitzWith_of_nnnorm_deriv_le (fun x => (rmRho_hasDerivAt x).differentiableAt) fun x => ?_
    rw [rmRho_deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]
    exact abs_rmRho'_le x
  have := hL.dist_le_mul a b
  simpa [Real.dist_eq] using this
end ReciprocityTheory.L2DbarEstimates.Y
