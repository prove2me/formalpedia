-- Prove2me | solution 1 for SZ.isQuadPisot_golden
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:55:43.107141+00:00
-- url     : https://prove2.me/submissions/8e779a99-d521-44c8-891e-be3044ac0749

import Definitions.Def_SZ_Silver
import Definitions.Def_SZ_Tijdeman
import Definitions.Def_SZ_QuadThm6
import Definitions.Def_SZ_GoldenS
import Mathlib.Tactic.LinearCombination
import Definitions.Def_SZ_Classification
import Theorems.Thm_SZ_one_lt_golden


set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution : IsQuadPisot golden := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : 2 < Real.sqrt 5 := by nlinarith
  have h2 : Real.sqrt 5 < 3 := by nlinarith
  refine ⟨one_lt_golden, (1 - Real.sqrt 5) / 2, 1, 1, ?_, ?_, ?_, ?_⟩
  · intro he
    rw [div_eq_zero_iff] at he
    rcases he with h | h <;> linarith
  · rw [abs_lt]
    constructor <;> [linarith; linarith]
  · rw [golden]; push_cast; ring
  · rw [golden]; push_cast; linear_combination (-1/4 : ℝ) * hsq
end SZ
