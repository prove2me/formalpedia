-- Prove2me | solution 1 for StarShapedRisk.Representation.proposition1_star_shaped_iff
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:15:40.384331+00:00
-- url     : https://prove2.me/submissions/a7857fd7-701e-4c22-9ad0-30430716f757

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_RiskMeasure
set_option autoImplicit false
open StarShapedRisk.Representation
theorem solution {Ω : Type*} (𝒳 : PositionSpace Ω) (ρ : 𝒳.carrier → ℝ)
    (hρ : IsRiskMeasure 𝒳 ρ) :
    List.TFAE
      [IsStarShaped 𝒳 ρ,
       ∀ (X : 𝒳.carrier) (α : ℝ), 0 < α → α < 1 → ρ (α • X) ≤ α * ρ X,
       ∀ X : 𝒳.carrier, MonotoneOn (fun β : ℝ => ρ (β • X) / β) (Set.Ioi 0)] := by
  tfae_have 1 → 2
  · intro hs X a ha0 ha1
    have hi : 1 < a⁻¹ := (one_lt_inv₀ ha0).mpr ha1
    have hh := hs (a • X) (a⁻¹) hi
    rw [smul_smul, inv_mul_cancel₀ ha0.ne', one_smul] at hh
    have hm := mul_le_mul_of_nonneg_left hh ha0.le
    simpa [← mul_assoc, mul_inv_cancel₀ ha0.ne'] using hm
  tfae_have 2 → 3
  · intro hc X a ha b hb hab
    change 0 < a at ha
    change 0 < b at hb
    rcases eq_or_lt_of_le hab with rfl | hab
    · exact le_rfl
    have hq0 : 0 < a / b := div_pos ha hb
    have hq1 : a / b < 1 := (div_lt_one hb).mpr hab
    have hh := hc (b • X) (a/b) hq0 hq1
    rw [smul_smul, div_mul_cancel₀ _ hb.ne'] at hh
    apply (div_le_div_iff₀ ha hb).mpr
    have hh' := mul_le_mul_of_nonneg_right hh hb.le
    field_simp at hh'
    nlinarith
  tfae_have 3 → 1
  · intro hm X t ht
    have hh := hm X (show (1:ℝ) ∈ Set.Ioi 0 by norm_num)
      (show t ∈ Set.Ioi 0 by exact lt_trans zero_lt_one ht) ht.le
    simp only [one_smul, div_one] at hh
    simpa [mul_comm] using (le_div_iff₀ (lt_trans zero_lt_one ht)).mp hh
  tfae_finish

