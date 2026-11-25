-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_birational_ratios_c3761376fe95
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:29:05.818988+00:00
-- url     : https://prove2.me/submissions/5c6a480d-236c-44ab-9523-eb2309978a21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinatesA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PBirationalCoordinates
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BirationalCoordinates_ratios_c_873ba0532ef9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isMultiHomog_X_ea0bbc06efc1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isMultiHomog_one_62c28c716664
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isMultiHomog_zero_48fd3347fd23
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_mhAdd_fc467322316c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_mhMul_fa685b51c398
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_mhNeg_939cfeec3808
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
variable {Ω : Type} [Field Ω] {κ : Type} [Fintype κ]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
theorem _root_.solution (x : Ix κ → Ω) {c : κ} (hc : x ⟨(), c⟩ ≠ 0) :
    Birational (ι := GlobalTheory κ) (ratios x c) := by
  intro s
  obtain ⟨s, hs⟩ := s
  induction hs using Subfield.closure_induction with
  | mem t ht =>
    obtain ⟨p, rfl⟩ := ht
    refine ⟨fun _ => 1, X p, X ⟨(), c⟩, ?_, ?_, ?_, ?_⟩
    · convert ProjLine.isMultiHomog_X (ι := GlobalTheory κ) p using 1
      funext k
      simp
    · convert ProjLine.isMultiHomog_X (ι := GlobalTheory κ) ⟨(), c⟩ using 1
      funext k
      simp
    · rw [aeval_X, ratios_c x hc]
      exact one_ne_zero
    · rw [aeval_X, aeval_X, ratios_c x hc, mul_one]
      rfl
  | one =>
    refine ⟨0, 1, 1, ProjLine.isMultiHomog_one, ProjLine.isMultiHomog_one, by simp, ?_⟩
    simp only [map_one, mul_one]
    rfl
  | add a b ha hb iha ihb =>
    obtain ⟨d₁, g₁, h₁, hg₁, hh₁, hne₁, he₁⟩ := iha
    obtain ⟨d₂, g₂, h₂, hg₂, hh₂, hne₂, he₂⟩ := ihb
    have hsum : IsMultiHomog (g₁ * h₂ + g₂ * h₁) (d₁ + d₂) := by
      refine ProjLine.mhAdd (ProjLine.mhMul hg₁ hh₂) ?_
      rw [add_comm d₁]
      exact ProjLine.mhMul hg₂ hh₁
    refine ⟨d₁ + d₂, g₁ * h₂ + g₂ * h₁, h₁ * h₂, hsum, ProjLine.mhMul hh₁ hh₂, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hne₁ hne₂
    · rw [map_add, map_mul, map_mul, map_mul, he₁, he₂]
      have : (⟨a + b, add_mem ha hb⟩ : ratioField x c) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
      rw [this]
      ring
  | neg a ha iha =>
    obtain ⟨d, g, h, hg, hh, hne, he⟩ := iha
    refine ⟨d, -g, h, ProjLine.mhNeg hg, hh, hne, ?_⟩
    rw [map_neg, he]
    have : (⟨-a, neg_mem ha⟩ : ratioField x c) = -⟨a, ha⟩ := rfl
    rw [this]
    ring
  | inv a ha iha =>
    obtain ⟨d, g, h, hg, hh, hne, he⟩ := iha
    by_cases ha0 : (⟨a, ha⟩ : ratioField x c) = 0
    · refine ⟨0, 0, 1, ProjLine.isMultiHomog_zero _, ProjLine.isMultiHomog_one, by simp, ?_⟩
      have : (⟨a⁻¹, inv_mem ha⟩ : ratioField x c) = (⟨a, ha⟩ : ratioField x c)⁻¹ := rfl
      rw [this, ha0]
      simp
    · have hg0 : aeval (ratios x c) g ≠ 0 := by
        rw [he]
        exact mul_ne_zero ha0 hne
      refine ⟨d, h, g, hh, hg, hg0, ?_⟩
      have : (⟨a⁻¹, inv_mem ha⟩ : ratioField x c) = (⟨a, ha⟩ : ratioField x c)⁻¹ := rfl
      rw [this, he]
      field_simp
  | mul a b ha hb iha ihb =>
    obtain ⟨d₁, g₁, h₁, hg₁, hh₁, hne₁, he₁⟩ := iha
    obtain ⟨d₂, g₂, h₂, hg₂, hh₂, hne₂, he₂⟩ := ihb
    refine ⟨d₁ + d₂, g₁ * g₂, h₁ * h₂, ProjLine.mhMul hg₁ hg₂, ProjLine.mhMul hh₁ hh₂, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hne₁ hne₂
    · rw [map_mul, map_mul, he₁, he₂]
      have : (⟨a * b, mul_mem ha hb⟩ : ratioField x c) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
      rw [this]
      ring
end GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates
