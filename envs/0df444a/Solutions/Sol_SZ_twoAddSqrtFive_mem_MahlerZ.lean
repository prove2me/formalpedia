-- Prove2me | solution 1 for SZ.twoAddSqrtFive_mem_MahlerZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:55:47.286831+00:00
-- url     : https://prove2.me/submissions/6bd0028a-0784-4266-9f70-d3da13cb28b3

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_SZ_QuadraticDesign
import Theorems.Thm_SZ_sqrtFive_pair
import Theorems.Thm_SZ_mem_MahlerZ_of_neg

section
namespace SZ
open Real Filter
variable {α β : ℝ} {a b : ℤ}
private theorem sqrt_five_facts :
    Real.sqrt 5 ^ 2 = 5 ∧ 2 < Real.sqrt 5 ∧ Real.sqrt 5 < 3 := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨hsq, ?_, ?_⟩ <;> nlinarith
end SZ
end

set_option autoImplicit false
open SZ
open Real Filter
variable {α β : ℝ} {a b : ℤ}
namespace SZ
theorem _root_.solution : (2 + Real.sqrt 5) ∈ MahlerZ := by
  obtain ⟨-, h2, h3⟩ := sqrt_five_facts
  exact mem_MahlerZ_of_neg sqrtFive_pair (by linarith) ⟨2, by ring⟩
    (by rintro ⟨k, hk⟩; omega)
end SZ
