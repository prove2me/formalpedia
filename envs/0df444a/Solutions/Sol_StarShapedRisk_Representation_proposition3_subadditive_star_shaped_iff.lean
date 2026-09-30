-- Prove2me | solution 1 for StarShapedRisk.Representation.proposition3_subadditive_star_shaped_iff
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:50:07.824335+00:00
-- url     : https://prove2.me/submissions/6903e35f-7e3f-48b6-bbfa-fd2700459ccb

import Definitions.Def_StarShapedRisk_Representation_RiskMeasure
import Mathlib.Tactic
open StarShapedRisk.Representation

private theorem star_small {Ω : Type*} (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ)
    (hs : IsStarShaped 𝒳 ρ) (X : 𝒳.carrier) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ρ (t • X) ≤ t * ρ X := by
  have hh := hs (t • X) t⁻¹ ((one_lt_inv₀ ht0).mpr ht1)
  rw [smul_smul,inv_mul_cancel₀ ht0.ne',one_smul] at hh
  have hm := mul_le_mul_of_nonneg_left hh ht0.le
  simpa [← mul_assoc,mul_inv_cancel₀ ht0.ne'] using hm

theorem solution {Ω : Type*} (𝒳 : PositionSpace Ω)
    (ρ : 𝒳.carrier → ℝ) (hρ : IsRiskMeasure 𝒳 ρ) (hsub : IsSubadditive 𝒳 ρ) :
    List.TFAE [IsStarShaped 𝒳 ρ, IsPositivelyHomogeneous 𝒳 ρ, IsConvex 𝒳 ρ] := by
  tfae_have 1 → 2
  · intro hs
    have hsmall (X : 𝒳.carrier) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : ρ (t • X)=t*ρ X := by
      have h1 := star_small 𝒳 ρ hs X t ht0 ht1
      have h2 := star_small 𝒳 ρ hs X (1-t) (by linarith) (by linarith)
      have h3 := hsub (t • X) ((1-t) • X)
      rw [← add_smul,add_sub_cancel,one_smul] at h3
      linarith
    intro X t ht
    rcases lt_trichotomy t 1 with h|rfl|h
    · exact hsmall X t ht h
    · simp
    · have hi0 : 0 < t⁻¹ := inv_pos.mpr ht
      have hi1 : t⁻¹ < 1 := (inv_lt_one₀ ht).mpr h
      have hh := hsmall (t • X) t⁻¹ hi0 hi1
      rw [smul_smul,inv_mul_cancel₀ ht.ne',one_smul] at hh
      have hm := congrArg (fun z => t*z) hh
      simpa [← mul_assoc,mul_inv_cancel₀ ht.ne'] using hm.symm
  tfae_have 2 → 3
  · intro hh X Y t ht0 ht1
    have hs := hsub (t • X) ((1-t) • Y)
    rw [hh X t ht0,hh Y (1-t) (by linarith)] at hs
    exact hs
  tfae_have 3 → 1
  · intro hc X t ht
    have ht0 : 0 < t := by linarith
    have hh := hc (t • X) 0 t⁻¹ (inv_pos.mpr ht0) ((inv_lt_one₀ ht0).mpr ht)
    simp only [smul_smul,inv_mul_cancel₀ ht0.ne',one_smul,smul_zero,add_zero,hρ.2.2,mul_zero] at hh
    have hn : ρ 0=0 := hρ.2.2
    rw [hn,mul_zero,add_zero] at hh
    have hm := mul_le_mul_of_nonneg_left hh ht0.le
    simpa [← mul_assoc,mul_inv_cancel₀ ht0.ne'] using hm
  tfae_finish
