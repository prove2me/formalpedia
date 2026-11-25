-- Prove2me | solution 1 for SZ.floor_witXi_sqrtThree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:05.69486+00:00
-- url     : https://prove2.me/submissions/cfec1e6d-0b70-4d61-bd13-093a438e5f7e

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
import Theorems.Thm_SZ_isDigits_digitY
import Theorems.Thm_SZ_coupling
import Theorems.Thm_SZ_exists_digitB_eq_two
import Theorems.Thm_SZ_floor_add_digitReal_mul_pow


set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution : ⌊witXi * Real.sqrt 3⌋ = 2 := by
  obtain ⟨i₀, hi₀, hz⟩ := exists_digitB_eq_two 0
  have hsmall : digitY i₀ ≤ ((3 : ℕ) : ℤ) - 2 := by simp [digitY, hz]
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hval : witXi * Real.sqrt 3
      = (((2 : ℤ) : ℝ) + digitReal 3 digitY) * ((3 : ℕ) : ℝ) ^ 0 := by
    rw [witXi, show (4 + witX) / 3 = Real.sqrt 3 * (2 + witY) / 3 by rw [coupling], witY]
    push_cast
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    ring
  rw [hval, floor_add_digitReal_mul_pow isDigits_digitY 2 0 hi₀ hsmall]
  simp
end SZ
