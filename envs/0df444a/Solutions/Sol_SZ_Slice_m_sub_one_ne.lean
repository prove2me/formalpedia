-- Prove2me | solution 1 for SZ.Slice.m_sub_one_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:01:24.502464+00:00
-- url     : https://prove2.me/submissions/2265c1f1-8f54-4acd-9f62-440e34ebf7cb

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
theorem _root_.solution : ((S.m : ℝ) - 1) ≠ 0 := by
  have := S.three_le_cast; intro h; linarith
end SZ.Slice
