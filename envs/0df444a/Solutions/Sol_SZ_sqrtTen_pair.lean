-- Prove2me | solution 1 for SZ.sqrtTen_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:44:13.952323+00:00
-- url     : https://prove2.me/submissions/62c5e00f-0d87-41d1-b01a-620f312b50c8

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_SZ_QuadraticDesign
section
namespace SZ
open Real Filter
variable {α β : ℝ} {a b : ℤ}
private theorem sqrt_ten_facts :
    Real.sqrt 10 ^ 2 = 10 ∧ 3 < Real.sqrt 10 ∧ Real.sqrt 10 < 4 := by
  have hsq : Real.sqrt 10 ^ 2 = 10 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 10 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨hsq, ?_, ?_⟩ <;> nlinarith
end SZ
end

set_option autoImplicit false
open SZ
open Real Filter
variable {α β : ℝ} {a b : ℤ}
namespace SZ
theorem _root_.solution : Pair (3 + Real.sqrt 10) (3 - Real.sqrt 10) 6 1 := by
  obtain ⟨hsq, h3, h4⟩ := sqrt_ten_facts
  exact { one_lt := by linarith
          absLt := by rw [abs_lt]; constructor <;> linarith
          sum := by push_cast; ring
          prod := by push_cast; linear_combination -hsq }
end SZ
