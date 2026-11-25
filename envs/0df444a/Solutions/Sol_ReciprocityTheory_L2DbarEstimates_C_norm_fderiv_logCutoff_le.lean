-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.norm_fderiv_logCutoff_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:08.722281+00:00
-- url     : https://prove2.me/submissions/eefd4884-cc14-42c8-a567-6d5e65d44306

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_fderiv_logCutoff

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
theorem _root_.solution {F : V n → ℂ} {k C : ℝ} (hk : 0 < k)
    (hC : ∀ t, ‖deriv extCh t‖ ≤ C) {z : V n} (hF : DifferentiableAt ℝ F z) (hz : F z ≠ 0) :
    ‖fderiv ℝ (extCut F k) z‖ ≤ C * k⁻¹ * ‖fderiv ℝ (fun w => Real.log (‖F w‖ ^ 2)) z‖ := by
  rw [fderiv_logCutoff hF hz, norm_smul, norm_smul, norm_neg, norm_inv,
    Real.norm_of_nonneg hk.le, ← mul_assoc]
  gcongr
  exact hC _
end ReciprocityTheory.L2DbarEstimates.C
