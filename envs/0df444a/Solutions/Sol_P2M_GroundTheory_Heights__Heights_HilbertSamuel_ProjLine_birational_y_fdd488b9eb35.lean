-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_birational_y_fdd488b9eb35
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:56:47.13674+00:00
-- url     : https://prove2.me/submissions/cd43f234-e3df-4a25-9533-c63f93d4525d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isMultiHomog_zero_48fd3347fd23
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isMultiHomog_one_62c28c716664
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_mhNeg_939cfeec3808
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_mhAdd_fc467322316c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_mhMul_fa685b51c398
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isMultiHomog_X_ea0bbc06efc1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.y_zero
attribute [local simp] GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.y_one

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
theorem _root_.solution : Birational (ι := GlobalTheory (Fin 2)) y := by
  intro s
  obtain ⟨s, hs⟩ := s
  induction hs using Subfield.closure_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨fun _ => 1, X ⟨(), 1⟩, X ⟨(), 0⟩, ?_, ?_, ?_, ?_⟩
    · convert isMultiHomog_X (ι := GlobalTheory (Fin 2)) ⟨(), 1⟩ using 1
      funext k
      simp
    · convert isMultiHomog_X (ι := GlobalTheory (Fin 2)) ⟨(), 0⟩ using 1
      funext k
      simp
    · simp
    · simp only [aeval_X, y_zero, y_one, mul_one]
      rfl
  | one =>
    refine ⟨0, 1, 1, isMultiHomog_one, isMultiHomog_one, by simp, ?_⟩
    simp only [map_one, mul_one]
    rfl
  | add a b ha hb iha ihb =>
    obtain ⟨d₁, g₁, h₁, hg₁, hh₁, hne₁, he₁⟩ := iha
    obtain ⟨d₂, g₂, h₂, hg₂, hh₂, hne₂, he₂⟩ := ihb
    have hsum : IsMultiHomog (g₁ * h₂ + g₂ * h₁) (d₁ + d₂) := by
      refine mhAdd (mhMul hg₁ hh₂) ?_
      rw [add_comm d₁]
      exact mhMul hg₂ hh₁
    refine ⟨d₁ + d₂, g₁ * h₂ + g₂ * h₁, h₁ * h₂, hsum, mhMul hh₁ hh₂, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hne₁ hne₂
    · rw [map_add, map_mul, map_mul, map_mul, he₁, he₂]
      have : (⟨a + b, add_mem ha hb⟩ : FnField) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
      rw [this]
      ring
  | neg a ha iha =>
    obtain ⟨d, g, h, hg, hh, hne, he⟩ := iha
    refine ⟨d, -g, h, mhNeg hg, hh, hne, ?_⟩
    rw [map_neg, he]
    have : (⟨-a, neg_mem ha⟩ : FnField) = -⟨a, ha⟩ := rfl
    rw [this]
    ring
  | inv a ha iha =>
    obtain ⟨d, g, h, hg, hh, hne, he⟩ := iha
    by_cases ha0 : (⟨a, ha⟩ : FnField) = 0
    · refine ⟨0, 0, 1, isMultiHomog_zero _, isMultiHomog_one, by simp, ?_⟩
      have : (⟨a⁻¹, inv_mem ha⟩ : FnField) = (⟨a, ha⟩ : FnField)⁻¹ := rfl
      rw [this, ha0]
      simp
    · have hg0 : aeval y g ≠ 0 := by
        rw [he]
        exact mul_ne_zero ha0 hne
      refine ⟨d, h, g, hh, hg, hg0, ?_⟩
      have : (⟨a⁻¹, inv_mem ha⟩ : FnField) = (⟨a, ha⟩ : FnField)⁻¹ := rfl
      rw [this, he]
      field_simp
  | mul a b ha hb iha ihb =>
    obtain ⟨d₁, g₁, h₁, hg₁, hh₁, hne₁, he₁⟩ := iha
    obtain ⟨d₂, g₂, h₂, hg₂, hh₂, hne₂, he₂⟩ := ihb
    refine ⟨d₁ + d₂, g₁ * g₂, h₁ * h₂, mhMul hg₁ hg₂, mhMul hh₁ hh₂, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hne₁ hne₂
    · rw [map_mul, map_mul, he₁, he₂]
      have : (⟨a * b, mul_mem ha hb⟩ : FnField) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
      rw [this]
      ring
end GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
