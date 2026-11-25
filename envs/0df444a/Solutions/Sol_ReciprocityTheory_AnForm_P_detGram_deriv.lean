-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.detGram_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:26.743375+00:00
-- url     : https://prove2.me/submissions/a0e91ad6-1a71-4473-b3a1-a3023eba1f4a

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDens
import Theorems.Thm_ReciprocityTheory_AnForm_P_detGram_line
import Theorems.Thm_ReciprocityTheory_AnForm_P_contDiff_detGram
import Theorems.Thm_ReciprocityTheory_AnForm_P_deriv_re_eval_zero
import Theorems.Thm_ReciprocityTheory_AnForm_P_det_gramPolyMinor_coeff_zero_one
import Theorems.Thm_ReciprocityTheory_AnForm_P_fderiv_line_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open MeasureTheory
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution : DetGramDerivStatement := by
  intro N hd m hm
  have hC := contDiff_detGram N hd m hm
  have hl : ∀ v, (fun s : ℝ => detGram N hd m hm (s • v)) =
      fun s : ℝ => ((Gm N hd m hm v).det.eval (s : ℂ)).re := fun v => funext (detGram_line N hd m hm v)
  refine ⟨hC, ?_, ?_⟩
  · have h := detGram_line N hd m hm 0 0
    rw [smul_zero] at h
    rw [h, Complex.ofReal_zero, ← Polynomial.coeff_zero_eq_eval_zero, (det_gramPolyMinor_coeff_zero_one N hd m hm 0).1,
      Complex.ofReal_re]
  · refine ContinuousLinearMap.ext fun v => ?_
    rw [fderiv_line_zero (hC.differentiable (by norm_num) 0) v, hl v, deriv_re_eval_zero,
      (det_gramPolyMinor_coeff_zero_one N hd m hm v).2]
    simp
end ReciprocityTheory.AnForm.P
