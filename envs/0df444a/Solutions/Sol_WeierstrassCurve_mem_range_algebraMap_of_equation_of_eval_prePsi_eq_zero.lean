-- Prove2me | solution 1 for WeierstrassCurve.mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/4ff38bb3-9c83-5260-841a-264542309662

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero

set_option autoImplicit false

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve R) (n : ℕ) (hn : IsUnit ((n : ℕ) : R))
    (x y : K) (hxy : (W.map (algebraMap R K)).toAffine.Equation x y)
    (hψ : ((W.map (algebraMap R K)).preΨ n).eval x = 0) :
    x ∈ Set.range (algebraMap R K) ∧ y ∈ Set.range (algebraMap R K) := by
  classical
  have hn0 : ((n : ℕ) : R) ≠ 0 := hn.ne_zero

  have hψ' : Polynomial.aeval x (W.preΨ' n) = 0 := by
    have : ((W.map (algebraMap R K)).preΨ n) = (W.preΨ' n).map (algebraMap R K) := by
      rw [WeierstrassCurve.map_preΨ, WeierstrassCurve.preΨ_ofNat]
    rw [this, Polynomial.eval_map, ← Polynomial.aeval_def] at hψ
    exact hψ
  have hlc : IsUnit (W.preΨ' n).leadingCoeff := by
    rw [W.leadingCoeff_preΨ' hn0]
    split_ifs with he
    · obtain ⟨m, hm⟩ := he
      have hnm : n / 2 = m := by omega
      rw [hnm]
      have : ((n : ℕ) : R) = (m : R) * 2 := by rw [hm]; push_cast; ring
      rw [this] at hn
      exact isUnit_of_mul_isUnit_left hn
    · exact hn
  obtain ⟨u, hu⟩ := hlc
  have hmonic : (Polynomial.C (↑u⁻¹ : R) * W.preΨ' n).Monic := by
    apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [← hu, Units.inv_mul]
  have hxint : _root_.IsIntegral R x := by
    refine ⟨Polynomial.C (↑u⁻¹ : R) * W.preΨ' n, hmonic, ?_⟩
    rw [← Polynomial.aeval_def, map_mul, hψ', mul_zero]
  obtain ⟨x₀, rfl⟩ := (isIntegrallyClosed_iff K).mp ‹IsIntegrallyClosed R› hxint
  refine ⟨⟨x₀, rfl⟩, ?_⟩

  set b : R := W.a₁ * x₀ + W.a₃ with hb
  set c : R := -(x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) with hc
  have heq : y ^ 2 + algebraMap R K b * y + algebraMap R K c = 0 := by
    rw [WeierstrassCurve.Affine.equation_iff] at hxy
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hxy
    rw [hb, hc]
    simp only [map_add, map_mul, map_neg, map_pow]
    linear_combination hxy
  let Q : Polynomial R := Polynomial.X ^ 2 + (Polynomial.C b * Polynomial.X + Polynomial.C c)
  have hQmonic : Q.Monic := by
    apply Polynomial.Monic.add_of_left (Polynomial.monic_X_pow 2)
    rw [Polynomial.degree_X_pow]
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) ?_
    refine max_lt ?_ ?_
    · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le b) (by norm_num)
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
  have hyint : _root_.IsIntegral R y := by
    refine ⟨Q, hQmonic, ?_⟩
    rw [← Polynomial.aeval_def]
    simp only [Q, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [← heq]; ring
  exact (isIntegrallyClosed_iff K).mp ‹IsIntegrallyClosed R› hyint

end S_WeierstrassCurve_mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_mem_range_algebraMap_of_equation_of_eval_prePsi_eq_zero (solution)
