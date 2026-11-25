-- Prove2me | solution 1 for SZ.Slice.M_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:25:36.440778+00:00
-- url     : https://prove2.me/submissions/36371fc3-8131-4518-9d01-6927fb0627e4

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_e_cast_le
import Theorems.Thm_SZ_Slice_m_sub_one_pos
import Theorems.Thm_SZ_Slice_M_mul

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
namespace SZ.Slice
theorem _root_.solution : S.M ≤ 1 := by
  have h := S.M_mul
  have h2 := S.e_cast_le
  have h3 := S.m_sub_one_pos
  nlinarith
end SZ.Slice
