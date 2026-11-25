-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.fsPot_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:34:56.37474+00:00
-- url     : https://prove2.me/submissions/5e063d5e-af47-48d3-a06b-6037a0672aab

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLineAtlas_chart0
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLineAtlas_chart1
import Theorems.Thm_ReciprocityTheory_AnForm_M_fsPot_U_infty
import Theorems.Thm_ReciprocityTheory_AnForm_M_fsPot_U_coe
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_fsPot___infty_ec505eb666d6
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_fsPot___coe_5dad99c71fe1
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
open MeasureTheory OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (x : OnePoint ℂ) : ∀ j : Fin 2,
    (fsPot.φ x ∘ (p1.chart j).symm = fun w => fubiniStudyProfile (fsQ w)) ∨
      ((fsPot.φ x ∘ (p1.chart j).symm = fun w => fubiniStudyProfileInv (fsQ w)) ∧
        ∀ w ∈ (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x, w 0 ≠ 0) := by
  intro j
  revert j
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · induction x with
    | infty =>
      right
      refine ⟨?_, fun w hw => projLineChart0_symm_ne_zero.1 (by rw [fsPot_U_infty] at hw; exact hw.2)⟩
      funext w
      rw [fsPot_φ_infty, projLineAtlas_chart0]
      simp only [Function.comp_apply, projLineChart0_symm_apply, infiniteCoord_coe, fubiniStudyProfileInv, fsQ, norm_inv, inv_pow]
    | coe z =>
      left
      funext w
      rw [fsPot_φ_coe, projLineAtlas_chart0]
      simp only [Function.comp_apply, projLineChart0_symm_apply, finiteCoord_coe, fubiniStudyProfile, fsQ]
  · induction x with
    | infty =>
      left
      funext w
      rw [fsPot_φ_infty, projLineAtlas_chart1]
      simp only [Function.comp_apply, infiniteCoord_projLineChart1_symm, fubiniStudyProfile, fsQ]
    | coe z =>
      right
      refine ⟨?_, fun w hw => projLineChart1_symm_mem_range.1 (by rw [fsPot_U_coe] at hw; exact hw.2)⟩
      funext w
      rw [fsPot_φ_coe, projLineAtlas_chart1]
      simp only [Function.comp_apply, finiteCoord_projLineChart1_symm, fubiniStudyProfileInv, fsQ, norm_inv, inv_pow]
end ReciprocityTheory.AnForm.M
