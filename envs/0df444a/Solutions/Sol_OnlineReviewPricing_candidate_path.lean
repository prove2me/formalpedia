-- Prove2me | solution 1 for OnlineReviewPricing.candidate_path
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:28:20.845367+00:00
-- url     : https://prove2.me/submissions/03ef79c8-2342-48b9-9c92-babfcb0d1889

import Mathlib
import Definitions.Def_OnlineReviewPricing_IsRootOf14
import Definitions.Def_OnlineReviewPricing_candidatePrice
import Definitions.Def_OnlineReviewPricing_candidatePath
import Definitions.Def_OnlineReviewPricing_IsFluidPath
import Definitions.Def_OnlineReviewPricing_demand

open OnlineReviewPricing in
theorem solution (μ μ₀ γ T z : ℝ) (hγ : 0 < γ) (hT : 0 < T) (hz : IsRootOf14 μ μ₀ γ T z) :
    IsFluidPath μ μ₀ γ T (candidatePrice μ μ₀ γ T z) (candidatePath z) ∧
      ∀ t ∈ Set.Icc 0 T,
        demand μ μ₀ γ (candidatePrice μ μ₀ γ T z t) (candidatePath z t) = ell z := by
  have hℓ0 : 0 < ell z := by
    unfold ell; exact div_pos (Real.exp_pos z) (by linarith [Real.exp_pos z])
  have hden : ∀ t : ℝ, 0 ≤ t → 0 < γ * (ell z * t) + 1 := by
    intro t ht
    have := mul_nonneg hγ.le (mul_nonneg hℓ0.le ht)
    linarith
  have hz' : z = μ - 1 + (μ₀ - μ) / (γ * (ell z * T) + 1) - Real.exp z := by
    unfold IsRootOf14 at hz
    rw [show γ * ell z * T = γ * (ell z * T) by ring] at hz
    linarith
  have key : ∀ t, 0 ≤ t →
      postMean μ μ₀ γ (candidatePath z t) - candidatePrice μ μ₀ γ T z t = z := by
    intro t ht
    unfold postMean candidatePrice candidatePath
    have hD1 : γ * (ell z * T) + 1 ≠ 0 := (hden T hT.le).ne'
    have hD2 : γ * (ell z * t) + 1 ≠ 0 := (hden t ht).ne'
    generalize ell z = ℓ at hD1 hD2 hz' ⊢
    generalize Real.exp z = E at hz' ⊢
    rw [hz']
    have hB : (γ * (ℓ * t) + 1) * (γ * (ℓ * t) + 1)⁻¹ = 1 := mul_inv_cancel₀ hD2
    simp only [div_eq_mul_inv, one_mul]
    linear_combination μ * hB
  have hdem : ∀ t, 0 ≤ t →
      demand μ μ₀ γ (candidatePrice μ μ₀ γ T z t) (candidatePath z t) = ell z := by
    intro t ht
    unfold demand
    rw [key t ht]
  have hcont : ∀ t : ℝ, 0 ≤ t → ContinuousAt (candidatePrice μ μ₀ γ T z) t := by
    intro t ht
    have hne : γ * (ell z * t) + 1 ≠ 0 := (hden t ht).ne'
    show ContinuousAt (fun s => 1 + Real.exp z +
      (μ - μ₀) * (1 / (γ * (ell z * T) + 1) - 1 / (γ * (ell z * s) + 1))) t
    fun_prop (disch := assumption)
  refine ⟨⟨⟨∅, by simp, fun t ht _ => (hcont t ht.1).continuousWithinAt,
      fun t ht => ⟨_, ((hcont t ht.1).tendsto).mono_left nhdsWithin_le_nhds⟩,
      fun t ht => ⟨_, ((hcont t ht.1.le).tendsto).mono_left nhdsWithin_le_nhds⟩⟩,
    ?_, ?_, ?_⟩, fun t ht => hdem t ht.1⟩
  · show ContinuousOn (fun t => ell z * t) (Set.Icc 0 T)
    exact (continuous_const.mul continuous_id).continuousOn
  · show ell z * 0 = 0
    rw [mul_zero]
  · intro t ht
    have ht0 : 0 ≤ t := ht.1
    rw [intervalIntegral.integral_congr (g := fun _ => ell z) (fun s hs => by
      rw [Set.uIcc_of_le ht0] at hs
      exact hdem s hs.1)]
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    show ell z * t = t * ell z
    ring
