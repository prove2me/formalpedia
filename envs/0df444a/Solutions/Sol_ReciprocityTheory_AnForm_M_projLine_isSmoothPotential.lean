-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.projLine_isSmoothPotential
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:30.472022+00:00
-- url     : https://prove2.me/submissions/f087ab3a-d146-4f86-a482-513fdbe543b0

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Theorems.Thm_ReciprocityTheory_AnForm_M_fsPot_U_infty
import Theorems.Thm_ReciprocityTheory_AnForm_M_fsPot_U_coe
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_fsPot___infty_ec505eb666d6
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_M_fsPot___coe_5dad99c71fe1
import Theorems.Thm_ReciprocityTheory_AnForm_M_fsPot_smooth
import Theorems.Thm_ReciprocityTheory_AnForm_M_holoOn_const
import Theorems.Thm_ReciprocityTheory_AnForm_M_fs_local
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


section
namespace ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
private theorem half_log_one_add_inv_sq_sub_eq_neg_log {ζ : ℂ} (h : ζ ≠ 0) :
    (1 / 2) * Real.log (1 + ‖ζ⁻¹‖ ^ 2) - (1 / 2) * Real.log (1 + ‖ζ‖ ^ 2) = -Real.log ‖ζ‖ := by
  have hn : 0 < ‖ζ‖ := norm_pos_iff.2 h
  have hn2 : ‖ζ‖ ^ 2 ≠ 0 := by positivity
  have h1 : 1 + ‖ζ⁻¹‖ ^ 2 = (1 + ‖ζ‖ ^ 2) / ‖ζ‖ ^ 2 := by
    rw [norm_inv, inv_pow, add_div, div_self hn2, one_div, add_comm]
  rw [h1, Real.log_div (by positivity) hn2, Real.log_pow]
  push_cast
  ring
end
end ReciprocityTheory.AnForm.M
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution : IsPotential p1 fsPot := by
  refine ⟨fsPot_smooth, ?_⟩
  intro x x' y hy
  induction x with
  | infty =>
    induction x' with
    | infty =>
      exact ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, holoOn_const _ 0, fun z _ => by simp⟩
    | coe z' =>
      obtain ⟨hy1, hy2⟩ := hy
      rw [fsPot_U_infty] at hy1
      rw [fsPot_U_coe] at hy2
      obtain ⟨ζ0, rfl⟩ := hy2
      have h0 : ζ0 ≠ 0 := fun h => hy1 (by rw [h])
      obtain ⟨W, hWo, hyW, G, hG, hGW⟩ := fs_local ζ0 h0
      refine ⟨W, hWo, hyW, fun z => -G z, fun j w hw => (hG j w hw).neg, ?_⟩
      rintro z ⟨⟨hzW, _⟩, _⟩
      obtain ⟨ζ, rfl, hζ, hre⟩ := hGW z hzW
      rw [fsPot_φ_infty, fsPot_φ_coe]
      simp only [infiniteCoord_coe, finiteCoord_coe, Complex.neg_re, hre]
      exact half_log_one_add_inv_sq_sub_eq_neg_log hζ
  | coe z =>
    induction x' with
    | infty =>
      obtain ⟨hy1, hy2⟩ := hy
      rw [fsPot_U_coe] at hy1
      rw [fsPot_U_infty] at hy2
      obtain ⟨ζ0, rfl⟩ := hy1
      have h0 : ζ0 ≠ 0 := fun h => hy2 (by rw [h])
      obtain ⟨W, hWo, hyW, G, hG, hGW⟩ := fs_local ζ0 h0
      refine ⟨W, hWo, hyW, G, hG, ?_⟩
      rintro z ⟨⟨hzW, _⟩, _⟩
      obtain ⟨ζ, rfl, hζ, hre⟩ := hGW z hzW
      rw [fsPot_φ_infty, fsPot_φ_coe]
      simp only [infiniteCoord_coe, finiteCoord_coe, hre]
      linarith [half_log_one_add_inv_sq_sub_eq_neg_log hζ]
    | coe z'' =>
      exact ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, holoOn_const _ 0, fun w _ => by
        simp [fsPot_φ_coe]⟩
end ReciprocityTheory.AnForm.M
