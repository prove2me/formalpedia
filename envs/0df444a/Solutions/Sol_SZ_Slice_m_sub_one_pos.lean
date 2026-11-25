-- Prove2me | solution 1 for SZ.Slice.m_sub_one_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:40:43.00661+00:00
-- url     : https://prove2.me/submissions/bcddd200-d185-4a53-a5f5-a2711924eb50

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_three_le_cast

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
namespace SZ.Slice
theorem _root_.solution : (0 : ℝ) < (S.m : ℝ) - 1 := by have := S.three_le_cast; linarith
end SZ.Slice
