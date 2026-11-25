-- Prove2me | solution 1 for SZ.even_floor_odd_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:57:41.413953+00:00
-- url     : https://prove2.me/submissions/eca62af1-c973-433e-bc5e-e293f2ec5812

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
import Theorems.Thm_SZ_digitY_even
import Theorems.Thm_SZ_isDigits_digitY
import Theorems.Thm_SZ_coupling
import Theorems.Thm_SZ_even_floor_add_digitReal_mul_pow
import Theorems.Thm_SZ_exists_digitB_eq_two


set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution (s : ℕ) : Even ⌊witXi * Real.sqrt 3 ^ (2 * s + 1)⌋ := by
  obtain ⟨i₀, hi₀, hz⟩ := exists_digitB_eq_two s
  have hsmall : digitY i₀ ≤ ((3 : ℕ) : ℤ) - 2 := by simp [digitY, hz]
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hval : witXi * Real.sqrt 3 ^ (2 * s + 1)
      = (((2 : ℤ) : ℝ) + digitReal 3 digitY) * ((3 : ℕ) : ℝ) ^ s := by
    rw [pow_succ, pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), witXi]
    have hc : 4 + witX = Real.sqrt 3 * (2 + witY) := coupling
    rw [show (4 + witX) / 3 = Real.sqrt 3 * (2 + witY) / 3 by rw [hc], witY]
    push_cast
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    ring
  rw [hval]
  exact even_floor_add_digitReal_mul_pow isDigits_digitY (by decide) digitY_even s hi₀ hsmall
end SZ
