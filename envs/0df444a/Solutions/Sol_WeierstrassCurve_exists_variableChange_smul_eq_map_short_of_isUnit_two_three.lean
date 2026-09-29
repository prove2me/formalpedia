-- Prove2me | solution 1 for WeierstrassCurve.exists_variableChange_smul_eq_map_short_of_isUnit_two_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ad86e54d-12a2-5056-b6ab-51856708b139

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_map_short_of_isUnit_two_three

set_option autoImplicit false

universe u

theorem solution
    {R₀ : Type u} [CommRing R₀] [IsDomain R₀]
    {K : Type u} [Field K] [Algebra R₀ K] [IsFractionRing R₀ K]
    (h2 : IsUnit ((2 : ℕ) : R₀)) (h3 : IsUnit ((3 : ℕ) : R₀)) (W : WeierstrassCurve K) :
    ∃ (C : WeierstrassCurve.VariableChange K) (a b : R₀),
      C • W = (⟨0, 0, 0, a, b⟩ : WeierstrassCurve R₀).map (algebraMap R₀ K) := by
  classical
  have hinj : Function.Injective (algebraMap R₀ K) := IsFractionRing.injective R₀ K
  have h2K : IsUnit (2 : K) := by
    have := h2.map (algebraMap R₀ K)
    rwa [map_natCast, Nat.cast_ofNat] at this
  have h3K : IsUnit (3 : K) := by
    have := h3.map (algebraMap R₀ K)
    rwa [map_natCast, Nat.cast_ofNat] at this
  letI : Invertible (2 : K) := h2K.invertible
  letI : Invertible (3 : K) := h3K.invertible

  obtain ⟨C₀, hC₀⟩ := W.exists_variableChange_isShortNF
  haveI := hC₀
  set W' := C₀ • W with hW'
  have ha₁ : W'.a₁ = 0 := W'.a₁_of_isShortNF
  have ha₂ : W'.a₂ = 0 := W'.a₂_of_isShortNF
  have ha₃ : W'.a₃ = 0 := W'.a₃_of_isShortNF

  obtain ⟨⟨d₁, hd₁⟩, p₁, hp₁⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors R₀) W'.a₄
  obtain ⟨⟨d₂, hd₂⟩, p₂, hp₂⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors R₀) W'.a₆
  simp only [Algebra.smul_def] at hp₁ hp₂
  have hd₁0 : d₁ ≠ 0 := nonZeroDivisors.ne_zero hd₁
  have hd₂0 : d₂ ≠ 0 := nonZeroDivisors.ne_zero hd₂
  set d : R₀ := d₁ * d₂ with hd
  have hdK : algebraMap R₀ K d ≠ 0 := (map_ne_zero_iff _ hinj).mpr (mul_ne_zero hd₁0 hd₂0)

  let u : Kˣ := (Units.mk0 (algebraMap R₀ K d) hdK)⁻¹
  refine ⟨⟨u, 0, 0, 0⟩ * C₀, d ^ 3 * d₂ * p₁, d ^ 5 * d₁ * p₂, ?_⟩
  rw [mul_smul, ← hW']
  have hu : ((u⁻¹ : Kˣ) : K) = algebraMap R₀ K d := by simp [u]
  ext
  · simp [WeierstrassCurve.variableChange_a₁, ha₁]
  · simp [WeierstrassCurve.variableChange_a₂, ha₁, ha₂]
  · simp [WeierstrassCurve.variableChange_a₃, ha₁, ha₃]
  · rw [WeierstrassCurve.variableChange_a₄, WeierstrassCurve.map_a₄]
    simp only [ha₁, ha₂, ha₃, mul_zero, zero_mul, sub_zero, add_zero, hu, hd, map_mul, map_pow, hp₁]
    ring
  · rw [WeierstrassCurve.variableChange_a₆, WeierstrassCurve.map_a₆]
    simp only [ha₁, ha₂, ha₃, mul_zero, zero_mul, sub_zero, add_zero, hu, hd, map_mul, map_pow, hp₂]
    ring

end S_WeierstrassCurve_exists_variableChange_smul_eq_map_short_of_isUnit_two_three
end P2MW
export P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_map_short_of_isUnit_two_three (solution)
