-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.integral_log_eval_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:02:04.092661+00:00
-- url     : https://prove2.me/submissions/08c7c7c2-0824-42fd-9c15-79c609509997

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_integral_Ioc_log_eval_eq_logMahlerMeasure
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_logMahlerMeasure_comp_C_mul_X_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (p : ℂ[X]) {c : ℂ} (hc : c ≠ 0) (hc1 : ‖c‖ ≤ 1) :
    ∫ t in Set.Ioc (0 : ℝ) 1,
        Real.log ‖p.eval (c * Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))‖ ≤
      ∫ t in Set.Ioc (0 : ℝ) 1, Real.log ‖p.eval (Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))‖ := by
  have h := integral_Ioc_log_eval_eq_logMahlerMeasure (p.comp (C c * X))
  simp only [eval_comp, eval_mul, eval_C, eval_X] at h
  rw [h, integral_Ioc_log_eval_eq_logMahlerMeasure]
  exact logMahlerMeasure_comp_C_mul_X_le p hc hc1
end ReciprocityTheory.MultiplicativeHeights
