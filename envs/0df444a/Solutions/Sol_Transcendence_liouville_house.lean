-- Prove2me | solution 1 for Transcendence.liouville_house
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:06:03.660716+00:00
-- url     : https://prove2.me/submissions/74580a12-df93-4884-a130-31e8adc294f7

import Mathlib

open NumberField

-- Liouville's inequality in house form, with an integer denominator: `N(cα)` is a nonzero
-- integer, and `|N(cα)| ≤ ‖σ(cα)‖ · house(cα)^(d-1)` (Mathlib's `norm_norm_le_norm_mul_house_pow`).
theorem solution {K : Type*} [Field K] [NumberField K] {α : K} (hα : α ≠ 0)
    {c : ℤ} (hc : c ≠ 0) (hcα : IsIntegral ℤ ((c : K) * α)) (σ : K →+* ℂ) :
    1 ≤ |(c : ℝ)| ^ Module.finrank ℚ K * ‖σ α‖ * house α ^ (Module.finrank ℚ K - 1) := by
  set d := Module.finrank ℚ K
  have hd : 1 ≤ d := Module.finrank_pos
  set γ : 𝓞 K := ⟨(c : K) * α, hcα⟩
  have hγ0 : γ ≠ 0 := fun h ↦ mul_ne_zero (Int.cast_ne_zero.mpr hc) hα
    (show algebraMap (𝓞 K) K γ = 0 by rw [h, map_zero])
  have h1 : (1 : ℝ) ≤ ‖Algebra.norm ℚ ((c : K) * α)‖ := by
    have hne : Algebra.norm ℤ γ ≠ 0 := Algebra.norm_ne_zero_iff.mpr hγ0
    rw [show (c : K) * α = algebraMap (𝓞 K) K γ from rfl, ← Algebra.coe_norm_int,
      ← Rat.norm_cast_real]
    push_cast
    rw [Real.norm_eq_abs, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hne
  refine h1.trans ((norm_norm_le_norm_mul_house_pow _ σ).trans ?_)
  have hh : house ((c : K) * α) ≤ |(c : ℝ)| * house α := by
    simpa using house_mul_le (c : K) α
  calc ‖σ ((c : K) * α)‖ * house ((c : K) * α) ^ (d - 1)
      ≤ (|(c : ℝ)| * ‖σ α‖) * (|(c : ℝ)| * house α) ^ (d - 1) :=
        mul_le_mul (le_of_eq (by rw [map_mul, norm_mul, map_intCast, Complex.norm_intCast]))
          (pow_le_pow_left₀ (house_nonneg _) hh _) (pow_nonneg (house_nonneg _) _) (by positivity)
  _ = |(c : ℝ)| ^ d * ‖σ α‖ * house α ^ (d - 1) := by
        rw [mul_pow]; nth_rw 3 [show d = (d - 1) + 1 by omega]; ring

#print axioms solution
