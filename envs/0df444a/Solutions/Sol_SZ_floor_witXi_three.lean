-- Prove2me | solution 1 for SZ.floor_witXi_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:15.376961+00:00
-- url     : https://prove2.me/submissions/83ac38ba-5b8a-41f5-98d6-ffcdf7a7c9f6

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
import Theorems.Thm_SZ_exists_digitA_eq_zero
import Theorems.Thm_SZ_floor_add_digitReal_mul_pow
import Theorems.Thm_SZ_isDigits_digitA


set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution : ⌊witXi * Real.sqrt 3 ^ 2⌋ = 4 := by
  obtain ⟨i₀, hi₀, hz⟩ := exists_digitA_eq_zero 0
  have hval : witXi * Real.sqrt 3 ^ 2
      = (((4 : ℤ) : ℝ) + digitReal 3 digitA) * ((3 : ℕ) : ℝ) ^ 0 := by
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), witXi, witX]
    push_cast
    ring
  rw [hval, floor_add_digitReal_mul_pow isDigits_digitA 4 0 hi₀ (by omega)]
  simp
end SZ
