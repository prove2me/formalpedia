-- Prove2me | solution 1 for SZ.even_floor_even_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:53:20.58937+00:00
-- url     : https://prove2.me/submissions/044c7364-b045-4b2e-bf55-a73be350ca20

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
import Theorems.Thm_SZ_digitA_even
import Theorems.Thm_SZ_even_floor_add_digitReal_mul_pow
import Theorems.Thm_SZ_exists_digitA_eq_zero
import Theorems.Thm_SZ_isDigits_digitA


set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution (s : ℕ) : Even ⌊witXi * Real.sqrt 3 ^ (2 * (s + 1))⌋ := by
  obtain ⟨i₀, hi₀, hz⟩ := exists_digitA_eq_zero s
  have hval : witXi * Real.sqrt 3 ^ (2 * (s + 1))
      = (((4 : ℤ) : ℝ) + digitReal 3 digitA) * ((3 : ℕ) : ℝ) ^ s := by
    rw [pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), witXi, witX]
    push_cast
    rw [pow_succ]
    ring
  rw [hval]
  exact even_floor_add_digitReal_mul_pow isDigits_digitA (by decide) digitA_even s hi₀
    (by omega)
end SZ
