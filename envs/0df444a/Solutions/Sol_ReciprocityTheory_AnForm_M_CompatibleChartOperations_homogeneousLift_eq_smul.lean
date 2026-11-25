-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.CompatibleChartOperations.homogeneousLift_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:00.929854+00:00
-- url     : https://prove2.me/submissions/b7b331c4-78f1-4ca0-b830-fc1556d867ee

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
import Theorems.Thm_ReciprocityTheory_AnForm_M_CompatibleChartOperations_fsPot_U_ite
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
theorem _root_.solution {a p : OnePoint ℂ} (h : p ∈ fsPot.U a) :
    ∃ c : ℂ, c ≠ 0 ∧ homogeneousLift a p = c • homogeneousCoord p := by
  rw [fsPot_U_ite] at h
  by_cases ha : a = ∞
  · rw [if_pos ha] at h
    induction p with
    | infty => exact ⟨1, one_ne_zero, by simp [homogeneousLift, ha, homogeneousCoord, crd1]⟩
    | coe z =>
      have hz : z ≠ 0 := fun hz => h (by rw [hz])
      refine ⟨z⁻¹, inv_ne_zero hz, ?_⟩
      simp [homogeneousLift, ha, homogeneousCoord, crd1, hz]
  · rw [if_neg ha] at h
    obtain ⟨z, rfl⟩ := h
    exact ⟨1, one_ne_zero, by simp [homogeneousLift, ha, homogeneousCoord, crd0]⟩
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
