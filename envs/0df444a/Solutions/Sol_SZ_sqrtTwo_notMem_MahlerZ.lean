-- Prove2me | solution 1 for SZ.sqrtTwo_notMem_MahlerZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:37:01.398519+00:00
-- url     : https://prove2.me/submissions/aa677c45-fe52-414c-8b63-18179011a7d2

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_SqrtTwo
import Theorems.Thm_SZ_eq_intCast_of_even_floors

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution : Real.sqrt 2 ∉ MahlerZ := by
  rintro ⟨-, ξ, hξ, hev⟩
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- the even exponents: `ξ (√2)^{2(k+1)} = (2ξ) 2ᵏ`
  have h1 : ∀ k : ℕ, Even ⌊2 * ξ * 2 ^ k⌋ := by
    intro k
    have e : 2 * ξ * 2 ^ k = ξ * Real.sqrt 2 ^ (2 * (k + 1)) := by
      rw [pow_mul, hsq, pow_succ]; ring
    rw [e]; exact hev _ (by omega)
  -- the odd exponents: `ξ (√2)^{2k+1} = (√2 ξ) 2ᵏ`
  have h2 : ∀ k : ℕ, Even ⌊Real.sqrt 2 * ξ * 2 ^ k⌋ := by
    intro k
    have e : Real.sqrt 2 * ξ * 2 ^ k = ξ * Real.sqrt 2 ^ (2 * k + 1) := by
      rw [pow_succ, pow_mul, hsq]; ring
    rw [e]; exact hev _ (by omega)
  obtain ⟨z₁, -, hz₁⟩ := eq_intCast_of_even_floors h1
  obtain ⟨z₂, -, hz₂⟩ := eq_intCast_of_even_floors h2
  have hz₁ne : ((z₁ : ℝ)) ≠ 0 := by rw [← hz₁]; exact mul_ne_zero two_ne_zero hξ
  refine irrational_sqrt_two ⟨(z₁ : ℚ) / (z₂ : ℚ), ?_⟩
  have hz₂ne : ((z₂ : ℝ)) ≠ 0 := by
    rw [← hz₂]
    exact mul_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))) hξ
  have hcancel : Real.sqrt 2 * (Real.sqrt 2 * ξ) = 2 * ξ := by
    rw [← mul_assoc, ← sq, hsq]
  push_cast
  rw [← hz₁, ← hz₂, div_eq_iff (by rw [hz₂]; exact hz₂ne)]
  exact hcancel.symm
end SZ
