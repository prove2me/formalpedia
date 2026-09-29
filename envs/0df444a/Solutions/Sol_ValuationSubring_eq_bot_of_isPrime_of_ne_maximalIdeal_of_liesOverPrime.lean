-- Prove2me | solution 1 for ValuationSubring.eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/1cce0533-0dd2-5750-9d9a-2dfbd3526a66

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime

set_option autoImplicit false

theorem solution
    {p : ℕ} (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (𝔮 : Ideal ↥A) [𝔮.IsPrime] (h𝔮 : 𝔮 ≠ IsLocalRing.maximalIdeal ↥A) : 𝔮 = ⊥ := by
  obtain ⟨μ, -, -, hmem⟩ := ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime hp A hA
  by_contra hne
  apply h𝔮

  refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
  obtain ⟨x, hx𝔮, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  intro y hy
  by_cases hy0 : y = 0
  · rw [hy0]; exact 𝔮.zero_mem

  have hxpos : 0 < μ (x : AlgebraicClosure ℚ) := μ.pos (by exact_mod_cast hx0)
  have hy1 : μ (y : AlgebraicClosure ℚ) < 1 := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy
    by_contra hge
    push_neg at hge
    apply hy
    have hyinv : (y : AlgebraicClosure ℚ)⁻¹ ∈ A := by
      rw [hmem, map_inv₀]
      exact inv_le_one_of_one_le₀ hge
    have hyne : (y : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hy0
    refine IsUnit.of_mul_eq_one ⟨_, hyinv⟩ ?_
    apply Subtype.ext
    show (y : AlgebraicClosure ℚ) * (y : AlgebraicClosure ℚ)⁻¹ = 1
    exact mul_inv_cancel₀ hyne

  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hxpos hy1

  have hq : ((y : AlgebraicClosure ℚ) ^ m * (x : AlgebraicClosure ℚ)⁻¹) ∈ A := by
    rw [hmem, map_mul, map_inv₀, map_pow]
    rw [mul_inv_le_iff₀ hxpos, one_mul]
    exact hm.le
  have hym : y ^ m = x * ⟨_, hq⟩ := by
    apply Subtype.ext
    show ((y : AlgebraicClosure ℚ)) ^ m = (x : AlgebraicClosure ℚ) * ((y : AlgebraicClosure ℚ) ^ m * (x : AlgebraicClosure ℚ)⁻¹)
    have hxne : (x : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hx0
    field_simp
  exact Ideal.IsPrime.mem_of_pow_mem inferInstance m (hym ▸ 𝔮.mul_mem_right _ hx𝔮)

end S_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime (solution)
