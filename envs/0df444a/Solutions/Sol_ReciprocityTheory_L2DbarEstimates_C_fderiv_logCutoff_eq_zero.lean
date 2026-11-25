-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.fderiv_logCutoff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:02:00.218335+00:00
-- url     : https://prove2.me/submissions/c67a3ba1-e18e-44c4-8e10-7ef65623f685

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_deriv_extCh_of_lt_one
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_deriv_extCh_of_two_lt
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
theorem _root_.solution {F : V n → ℂ} {k : ℝ} (hk : 0 < k) {z : V n}
    (hF : DifferentiableAt ℝ F z) (hz : F z ≠ 0)
    (h : ¬ (k ≤ -Real.log (‖F z‖ ^ 2) ∧ -Real.log (‖F z‖ ^ 2) ≤ 2 * k)) :
    fderiv ℝ (extCut F k) z = 0 := by
  rw [fderiv_logCutoff hF hz]
  set a := -Real.log (‖F z‖ ^ 2) with ha
  have hd : deriv extCh (a / k) = 0 := by
    by_cases h1 : k ≤ a
    · have h2 : 2 * k < a := by
        push_neg at h
        exact h h1
      exact deriv_extCh_of_two_lt ((lt_div_iff₀ hk).2 (by linarith))
    · push_neg at h1
      exact deriv_extCh_of_lt_one ((div_lt_one hk).2 h1)
  rw [hd, zero_smul]
end ReciprocityTheory.L2DbarEstimates.C
