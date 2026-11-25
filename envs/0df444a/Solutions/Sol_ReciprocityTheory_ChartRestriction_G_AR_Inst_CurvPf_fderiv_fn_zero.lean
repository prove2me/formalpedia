-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.fderiv_fn_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:03:45.478379+00:00
-- url     : https://prove2.me/submissions/e3f409ca-4516-4228-9e57-5a5f43e4b9fe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoeffMatrixZeroCorrectedLineGramPoly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DiagonalCurvatureCoefficient
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_contDiff_fn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_fn_line
import Theorems.Thm_ReciprocityTheory_AnForm_P_deriv_re_eval_zero
import Theorems.Thm_ReciprocityTheory_AnForm_P_det_coeff_zero_one_of_coeffMatrix_one
import Theorems.Thm_ReciprocityTheory_AnForm_P_fderiv_line_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_coeffMatrix_one_correctedLineGramPoly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Polynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P Filter Topology
variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
theorem _root_.solution : fderiv ℝ (fn hm D Y) 0 = 0 := by
  refine ContinuousLinearMap.ext fun w => ?_
  set t := w 0 with ht
  have hw : w = fun _ => t := funext fun i => by fin_cases i; rfl
  rw [fderiv_line_zero (((contDiff_fn hm D Y).differentiable (by norm_num)) 0), hw]
  have e : (fun s : ℝ => fn hm D Y (s • fun _ => t)) = fun s : ℝ => ((GnP hm D Y t).det.eval (s : ℂ)).re :=
    funext (fn_line hm D Y t)
  rw [e, deriv_re_eval_zero, (det_coeff_zero_one_of_coeffMatrix_one _ (coeffMatrix_one_correctedLineGramPoly hm D Y t)).2]
  simp
end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
