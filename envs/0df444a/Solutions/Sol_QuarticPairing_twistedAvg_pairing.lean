-- Prove2me | solution 1 for QuarticPairing.twistedAvg_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:37:35.670051+00:00
-- url     : https://prove2.me/submissions/48586ac9-e6bd-472d-a571-d0258d810939

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
theorem _root_.solution (χ χ₃ g : GaussianInt → ℂ) (w : GaussianInt → ℝ)
    (s : Finset GaussianInt) {κ : ℂ} (hκ : ‖κ‖ = 1)
    (hχ : ∀ c ∈ s, w c ≠ 0 → starRingEnd ℂ (χ₃ c) = χ c)
    (h12 : ∀ c ∈ s, w c ≠ 0 → g c = 0 ∨ g c ^ 2 = -κ * unitDir c) (k : ℤ) :
    twistedAvg χ₃ g w s (-k - 1) = -κ * starRingEnd ℂ (twistedAvg χ g w s k) := by
  unfold twistedAvg
  rw [map_sum, mul_sum]
  refine sum_congr rfl fun c hc => ?_
  by_cases hw : w c = 0
  · simp [hw]
  rcases h12 c hc hw with hg | hg
  · simp [hg]
  by_cases hg0 : g c = 0
  · simp [hg0]
  have hθ0 := unitDir_ne_zero_of hg0 hg
  have hc0 : c ≠ 0 := by rintro rfl; exact hθ0 unitDir_zero
  have hθ := norm_unitDir hc0
  have hpair := mul_conj_eq_neg_conj hθ hκ (Or.inr hg)
  have hκκ := mul_conj_self_eq_one hκ
  have hconjθ : starRingEnd ℂ (unitDir c) = (unitDir c)⁻¹ :=
    eq_inv_of_mul_eq_one_right (mul_conj_self_eq_one hθ)
  -- `conj g = -conj κ · g · conj θ`
  have hcg : starRingEnd ℂ (g c) = -starRingEnd ℂ κ * g c * starRingEnd ℂ (unitDir c) := by
    linear_combination (starRingEnd ℂ κ) * hpair - starRingEnd ℂ (g c) * hκκ
  rw [hχ c hc hw]
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, map_zpow₀]
  rw [hcg, hconjθ, inv_zpow, zpow_sub_one₀ hθ0, zpow_neg]
  linear_combination (-(χ c * g c * ((unitDir c) ^ k)⁻¹ * (unitDir c)⁻¹ * (w c : ℂ))) * hκκ
end QuarticPairing
