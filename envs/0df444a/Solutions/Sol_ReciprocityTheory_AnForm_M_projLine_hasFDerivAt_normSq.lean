-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.projLine_hasFDerivAt_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:53.8638+00:00
-- url     : https://prove2.me/submissions/5a321857-1d5b-49a6-8458-0ab0ba723a5c

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_dNormSq_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_norm_sq_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (w : Fin 1 → ℂ) :
    HasFDerivAt (fun w : Fin 1 → ℂ => ‖w 0‖ ^ 2) (projectiveLineNormSqDerivative w) w := by
  have h : (fun w : Fin 1 → ℂ => ‖w 0‖ ^ 2) = fun w => p1Re w * p1Re w + p1Im w * p1Im w := by
    funext w
    rw [projLine_norm_sq_eq]
    rfl
  rw [h]
  have h2 : HasFDerivAt (fun w => p1Re w * p1Re w + p1Im w * p1Im w)
      ((p1Re w • p1Re + p1Re w • p1Re) + (p1Im w • p1Im + p1Im w • p1Im)) w :=
    (p1Re.hasFDerivAt.mul p1Re.hasFDerivAt).add (p1Im.hasFDerivAt.mul p1Im.hasFDerivAt)
  convert h2 using 1
  ext v
  rw [dNormSq_apply]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, rea_apply,
    ima_apply]
  ring
end ReciprocityTheory.AnForm.M
