-- Prove2me | solution 1 for Polynomial.valuation_div_sub_one_lt_one_of_kroneckerShape
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c432d36c-cc79-52b3-8b58-5c93843c2da3

import Mathlib
import Theorems.Thm_Polynomial_valuation_root_dichotomy_of_kroneckerShape
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_valuation_div_sub_one_lt_one_of_kroneckerShape

set_option autoImplicit false

open Polynomial

theorem solution
    {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    {q : ℕ} (hq : 1 < q) (x₀ c : K) (hx : 1 < v x₀) (hc : v c ≤ 1)
    (H : K[X]) (hHdeg : H.natDegree ≤ q)
    (hHb : ∀ b < q, v (H.coeff b) ≤ v x₀ ^ q) (hHq : v (H.coeff q) ≤ v x₀ ^ (q - 1))
    (y : K) (hy : ((C (x₀ ^ q) - X) * (C x₀ - X ^ q) + C c * H).IsRoot y) :
    v (y / x₀ ^ q - 1) < 1 ∨ (1 < v y ∧ v (x₀ / y ^ q - 1) < 1) := by
  have hX0 : 0 < v x₀ := lt_trans zero_lt_one hx
  have hx0 : x₀ ≠ 0 := fun h => by simp [h] at hx
  have hq0 : q ≠ 0 := by omega
  have hqq : q = (q - 1) + 1 := by omega
  rcases Polynomial.valuation_root_dichotomy_of_kroneckerShape v hq x₀ c hx hc H hHdeg hHb hHq y hy
    with ⟨hs, hclose⟩ | ⟨hs, hclose⟩
  · left
    have hxq : x₀ ^ q ≠ 0 := pow_ne_zero _ hx0
    rw [div_sub_one hxq, map_div₀, map_pow, div_lt_one₀ (pow_pos hX0 _)]
    refine lt_of_le_of_lt hclose ?_
    calc v c * v x₀ ^ (q - 1) ≤ 1 * v x₀ ^ (q - 1) := mul_le_mul_of_nonneg_right hc zero_le'
      _ < v x₀ * v x₀ ^ (q - 1) := mul_lt_mul_of_pos_right hx (pow_pos hX0 _)
      _ = v x₀ ^ q := by conv_rhs => rw [hqq, pow_succ]; rw [mul_comm]
  · right
    have hs1 : 1 < v y := by
      by_contra h
      exact absurd (lt_of_lt_of_le hx (hs.symm.le.trans (pow_le_one₀ zero_le' (not_lt.mp h)))) (lt_irrefl _)
    have hy0 : y ≠ 0 := fun h => by simp [h] at hs1
    have hs0 : 0 < v y := lt_trans zero_lt_one hs1
    refine ⟨hs1, ?_⟩
    have hyq : y ^ q ≠ 0 := pow_ne_zero _ hy0
    rw [div_sub_one hyq, map_div₀, map_pow, div_lt_one₀ (pow_pos hs0 _)]
    refine lt_of_le_of_lt hclose ?_
    calc v c * v y ^ (q - 1) ≤ 1 * v y ^ (q - 1) := mul_le_mul_of_nonneg_right hc zero_le'
      _ < v y * v y ^ (q - 1) := mul_lt_mul_of_pos_right hs1 (pow_pos hs0 _)
      _ = v y ^ q := by conv_rhs => rw [hqq, pow_succ]; rw [mul_comm]

end S_Polynomial_valuation_div_sub_one_lt_one_of_kroneckerShape
end P2MW
export P2MW.S_Polynomial_valuation_div_sub_one_lt_one_of_kroneckerShape (solution)
