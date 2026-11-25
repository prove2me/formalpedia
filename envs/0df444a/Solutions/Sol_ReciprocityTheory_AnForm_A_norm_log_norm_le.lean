-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.norm_log_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:41.929354+00:00
-- url     : https://prove2.me/submissions/643bc46b-99a9-4bce-a0ed-412b0c72daf5

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogIntSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (z : ℂ) :
    ‖Real.log ‖z‖‖ ≤ ‖Real.log z.re‖ + ‖Real.log z.im‖ + ‖z.re‖ + ‖z.im‖ := by
  simp only [Real.norm_eq_abs]
  have hre := Complex.abs_re_le_norm z
  have him := Complex.abs_im_le_norm z
  have hsum := Complex.norm_le_abs_re_add_abs_im z
  have a1 := abs_nonneg (Real.log z.re)
  have a2 := abs_nonneg (Real.log z.im)
  have a3 := abs_nonneg z.re
  have a4 := abs_nonneg z.im
  rcases le_or_gt 1 ‖z‖ with h1 | h1
  · have h2 := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < ‖z‖)
    rw [abs_of_nonneg (Real.log_nonneg h1)]
    linarith
  · rcases eq_or_lt_of_le (norm_nonneg z) with h0 | h0
    · rw [← h0, Real.log_zero, abs_zero]
      positivity
    · rw [abs_of_neg (Real.log_neg h0 h1)]
      by_cases hr : z.re = 0
      · have hi : z.im ≠ 0 := by
          intro hi
          have hz : z = 0 := Complex.ext hr hi
          rw [hz, norm_zero] at h0
          exact lt_irrefl _ h0
        have h3 : Real.log |z.im| ≤ Real.log ‖z‖ := Real.log_le_log (abs_pos.mpr hi) him
        rw [Real.log_abs] at h3
        have h4 := neg_le_abs (Real.log z.im)
        linarith
      · have h3 : Real.log |z.re| ≤ Real.log ‖z‖ := Real.log_le_log (abs_pos.mpr hr) hre
        rw [Real.log_abs] at h3
        have h4 := neg_le_abs (Real.log z.re)
        linarith
end ReciprocityTheory.AnForm.A
