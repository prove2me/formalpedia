-- Prove2me | solution 2 for P2M_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_wd_cexp__5e52f4ad6c5d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:18:23.420904+00:00
-- url     : https://prove2.me/submissions/f9515477-34f5-40ab-9b54-977be1bf49f3

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
theorem _root_.solution (n : ℕ) (j : Fin n) (g : V n → ℂ) (y : V n) (hg : DifferentiableAt ℝ g y) :
    wd n j (fun w => Complex.exp (g w)) y = Complex.exp (g y) * wd n j g y := by
  simp only [wd, hg.hasFDerivAt.cexp.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
end ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
