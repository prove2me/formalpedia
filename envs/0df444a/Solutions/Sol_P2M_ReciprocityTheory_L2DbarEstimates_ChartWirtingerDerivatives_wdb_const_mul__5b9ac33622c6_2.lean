-- Prove2me | solution 2 for P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wdb_const_mul__5b9ac33622c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:16:31.039832+00:00
-- url     : https://prove2.me/submissions/06a91800-001f-45ce-b1a1-655f0a4c74b1

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
open Filter Topology Set
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
theorem _root_.solution (n : ℕ) (j : Fin n) (c : ℂ) (g : V n → ℂ) (y : V n)
    (hg : DifferentiableAt ℝ g y) : wdb n j (fun w => c * g w) y = c * wdb n j g y := by
  simp only [wdb, fderiv_const_mul hg c, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
end ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
