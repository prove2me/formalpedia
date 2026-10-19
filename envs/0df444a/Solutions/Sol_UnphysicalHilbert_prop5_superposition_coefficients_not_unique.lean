-- Prove2me | solution 1 for UnphysicalHilbert.prop5_superposition_coefficients_not_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:45:20.15859+00:00
-- url     : https://prove2.me/submissions/d7147e9c-14f9-4fa5-80f4-8f3fd369d4b6

import Mathlib

theorem solution
    {H : Type*} [AddCommGroup H] [Module ℂ H]
    (ψ ϕ₁ ϕ₂ : H) (hϕ₁ : ϕ₁ ≠ 0) (hϕ₂ : ϕ₂ ≠ 0) (c₁ c₂ : ℂ) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hψ : ψ = c₁ • ϕ₁ + c₂ • ϕ₂) (d₁ d₂ : ℂ) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
    ∃ (χ₁ χ₂ : H) (hχ₁ : χ₁ ≠ 0) (hχ₂ : χ₂ ≠ 0),
      Projectivization.mk ℂ χ₁ hχ₁ = Projectivization.mk ℂ ϕ₁ hϕ₁ ∧
      Projectivization.mk ℂ χ₂ hχ₂ = Projectivization.mk ℂ ϕ₂ hϕ₂ ∧
      ψ = d₁ • χ₁ + d₂ • χ₂ := by
  refine ⟨(c₁ / d₁) • ϕ₁, (c₂ / d₂) • ϕ₂, smul_ne_zero (div_ne_zero hc₁ hd₁) hϕ₁,
    smul_ne_zero (div_ne_zero hc₂ hd₂) hϕ₂, ?_, ?_, ?_⟩
  · rw [Projectivization.mk_eq_mk_iff]
    exact ⟨Units.mk0 (c₁ / d₁) (div_ne_zero hc₁ hd₁), rfl⟩
  · rw [Projectivization.mk_eq_mk_iff]
    exact ⟨Units.mk0 (c₂ / d₂) (div_ne_zero hc₂ hd₂), rfl⟩
  · rw [hψ, smul_smul, smul_smul, mul_div_cancel₀ _ hd₁, mul_div_cancel₀ _ hd₂]
