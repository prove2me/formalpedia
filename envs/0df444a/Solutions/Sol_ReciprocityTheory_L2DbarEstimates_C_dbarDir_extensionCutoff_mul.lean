-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.dbarDir_extensionCutoff_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:04:58.346373+00:00
-- url     : https://prove2.me/submissions/adbba212-3999-4ffa-a3df-0e8d8bbb664e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal ContDiff
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {F g : V n → ℂ} {k : ℝ} {z : V n} (v : V n)
    (hc : DifferentiableAt ℝ (extCut F k) z) (hg : DifferentiableAt ℝ g z) :
    dbarDir (fun w => (extCut F k w : ℂ) * g w) z v =
      (extCut F k z : ℂ) * dbarDir g z v + g z * ((fderiv ℝ (extCut F k) z (I • v) : ℂ) -
        I * (fderiv ℝ (extCut F k) z v : ℂ)) := by
  have hcC : HasFDerivAt (fun w => (extCut F k w : ℂ))
      (ofRealCLM.comp (fderiv ℝ (extCut F k) z)) z :=
    ofRealCLM.hasFDerivAt.comp z hc.hasFDerivAt
  unfold dbarDir
  have hm : HasFDerivAt (fun w => (extCut F k w : ℂ) * g w)
      ((extCut F k z : ℂ) • fderiv ℝ g z + g z • (ofRealCLM.comp (fderiv ℝ (extCut F k) z))) z :=
    hcC.mul hg.hasFDerivAt
  rw [hm.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, ofRealCLM_apply]
  ring
end ReciprocityTheory.L2DbarEstimates.C
