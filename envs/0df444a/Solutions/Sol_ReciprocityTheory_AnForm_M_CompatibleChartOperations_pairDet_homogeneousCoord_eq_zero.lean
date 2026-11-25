-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.CompatibleChartOperations.pairDet_homogeneousCoord_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:57.702699+00:00
-- url     : https://prove2.me/submissions/28a79cc7-705a-4377-abf5-73b0cdfcd941

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open OnePoint
noncomputable section
open ReciprocityTheory.AnForm.M.CompatibleChartOperations
namespace ReciprocityTheory.AnForm.M.CompatibleChartOperations
theorem _root_.solution {p q : OnePoint ℂ} (h : det2 (homogeneousCoord p) (homogeneousCoord q) = 0) : p = q := by
  induction p with
  | infty =>
    induction q with
    | infty => rfl
    | coe w => simp [homogeneousCoord, det2] at h
  | coe z =>
    induction q with
    | infty => simp [homogeneousCoord, det2] at h
    | coe w =>
      simp [homogeneousCoord, det2, sub_eq_zero] at h
      rw [h]
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
