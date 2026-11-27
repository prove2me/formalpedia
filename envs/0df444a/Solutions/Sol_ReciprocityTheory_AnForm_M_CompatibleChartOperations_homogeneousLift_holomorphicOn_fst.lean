-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.CompatibleChartOperations.homogeneousLift_holomorphicOn_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:25:16.341397+00:00
-- url     : https://prove2.me/submissions/8401f669-e443-4fab-b61a-24ac13f6cc2d

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
theorem _root_.solution (a : OnePoint ℂ) : p1.HoloOn (fsPot.U a) (fun p => (homogeneousLift a p).1) := by
  by_cases ha : a = ∞
  · have e : (fun p => (homogeneousLift a p).1) = crd1 := by
      funext p
      simp [homogeneousLift, ha]
    rw [e, fsPot_U_ite, if_pos ha]
    unfold FinHolAtlas.HoloOn
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · show AnalyticOnNhd ℂ (crd1 ∘ projectiveLineChartAtZero.symm) (projectiveLineChartAtZero.target ∩ projectiveLineChartAtZero.symm ⁻¹' projectiveLineChartAtInfinity.source)
      intro w hw
      have hw0 : w 0 ≠ 0 := projLineChart0_symm_ne_zero.1 hw.2
      have e2 : (crd1 ∘ projectiveLineChartAtZero.symm) = fun w : Fin 1 → ℂ => (w 0)⁻¹ := by
        funext w
        rfl
      rw [e2]
      exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt w).inv hw0
    · show AnalyticOnNhd ℂ (crd1 ∘ projectiveLineChartAtInfinity.symm) (projectiveLineChartAtInfinity.target ∩ projectiveLineChartAtInfinity.symm ⁻¹' projectiveLineChartAtInfinity.source)
      intro w _
      have e2 : (crd1 ∘ projectiveLineChartAtInfinity.symm) = fun w : Fin 1 → ℂ => w 0 := by
        funext w
        exact infiniteCoord_projLineChart1_symm w
      rw [e2]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt w
  · have e : (fun p => (homogeneousLift a p).1) = fun _ => (1 : ℂ) := by
      funext p
      simp [homogeneousLift, ha]
    rw [e]
    exact fun j w _ => analyticAt_const
end ReciprocityTheory.AnForm.M.CompatibleChartOperations
