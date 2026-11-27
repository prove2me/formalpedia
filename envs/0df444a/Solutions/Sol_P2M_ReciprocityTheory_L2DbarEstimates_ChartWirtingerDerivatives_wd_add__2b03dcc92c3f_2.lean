-- Prove2me | solution 2 for P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_add__2b03dcc92c3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:13:43.55583+00:00
-- url     : https://prove2.me/submissions/d1605c6f-da32-4e14-9022-e5ff2f18af78

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
theorem _root_.solution (n : ℕ) (j : Fin n) (g h : V n → ℂ) (y : V n) (hg : DifferentiableAt ℝ g y)
    (hh : DifferentiableAt ℝ h y) : wd n j (fun w => g w + h w) y = wd n j g y + wd n j h y := by
  simp only [wd, fderiv_fun_add hg hh, ContinuousLinearMap.add_apply]
  ring
end ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
