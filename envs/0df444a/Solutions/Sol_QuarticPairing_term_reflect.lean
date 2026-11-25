-- Prove2me | solution 1 for QuarticPairing.term_reflect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:37:34.863234+00:00
-- url     : https://prove2.me/submissions/a3a2dd5e-6d4d-4ee3-9dc2-330d26e587d4

module
public import Definitions.Def_QuarticPairing_Defs
public import Definitions.Def_QuarticPairing_Pairing
public import Theorems.Thm_QuarticPairing_mul_conj_self_eq_one
public import Theorems.Thm_QuarticPairing_mul_conj_eq_neg_conj
public import Theorems.Thm_QuarticPairing_norm_unitDir
public import Theorems.Thm_QuarticPairing_unitDir_zero
public import Theorems.Thm_QuarticPairing_unitDir_ne_zero_of

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
noncomputable section
open QuarticPairing
namespace QuarticPairing
theorem _root_.solution (g κ : ℂ) (hκ : ‖κ‖ = 1) (c : GaussianInt) (Λ : ℝ)
    (h : Λ ≠ 0 → g = 0 ∨ g ^ 2 = -κ * unitDir c) (ℓ : ℤ) :
    g * starRingEnd ℂ (unitDir c) ^ (1 - ℓ) * (Λ : ℂ) =
      -κ * starRingEnd ℂ (g * starRingEnd ℂ (unitDir c) ^ ℓ * (Λ : ℂ)) := by
  by_cases hΛ : Λ = 0
  · simp [hΛ]
  rcases h hΛ with hg | hg
  · simp [hg]
  by_cases hg0 : g = 0
  · simp [hg0]
  have hθ0 := unitDir_ne_zero_of hg0 hg
  have hc0 : c ≠ 0 := by rintro rfl; exact hθ0 unitDir_zero
  have hθ := norm_unitDir hc0
  have hpair := mul_conj_eq_neg_conj hθ hκ (Or.inr hg)
  have hκκ := mul_conj_self_eq_one hκ
  have hθθ := mul_conj_self_eq_one hθ
  have hφ0 : starRingEnd ℂ (unitDir c) ≠ 0 := (map_ne_zero _).2 hθ0
  have hθinv : unitDir c = (starRingEnd ℂ (unitDir c))⁻¹ := eq_inv_of_mul_eq_one_left hθθ
  have hθl : unitDir c ^ ℓ = (starRingEnd ℂ (unitDir c) ^ ℓ)⁻¹ := by
    conv_lhs => rw [hθinv]
    exact inv_zpow _ _
  have hcg : starRingEnd ℂ g = -starRingEnd ℂ κ * g * starRingEnd ℂ (unitDir c) := by
    linear_combination (starRingEnd ℂ κ) * hpair - starRingEnd ℂ g * hκκ
  simp only [map_mul, map_zpow₀, Complex.conj_conj, Complex.conj_ofReal]
  rw [hcg, hθl, zpow_sub₀ hφ0, zpow_one, div_eq_mul_inv]
  linear_combination (-(g * starRingEnd ℂ (unitDir c) * (starRingEnd ℂ (unitDir c) ^ ℓ)⁻¹ *
    (Λ : ℂ))) * hκκ
end QuarticPairing
