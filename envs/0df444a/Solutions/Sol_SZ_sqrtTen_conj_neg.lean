-- Prove2me | solution 1 for SZ.sqrtTen_conj_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:44:21.889999+00:00
-- url     : https://prove2.me/submissions/58000911-1e60-4061-bb1d-d175d8d777c1

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
theorem _root_.solution : (3 : ℝ) - Real.sqrt 10 < 0 := by
  obtain ⟨-, h3, -⟩ := sqrt_ten_facts; linarith
end SZ
