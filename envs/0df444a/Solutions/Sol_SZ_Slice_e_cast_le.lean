-- Prove2me | solution 1 for SZ.Slice.e_cast_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:24:15.045563+00:00
-- url     : https://prove2.me/submissions/3d95f32b-313b-4dc1-94a3-792df311cb72

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
namespace SZ.Slice
theorem _root_.solution : (S.e : ℝ) ≤ (S.m : ℝ) - 1 := by
  have := S.e_le
  have : ((S.e : ℤ) : ℝ) ≤ (((S.m : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast this
  push_cast at this
  linarith
end SZ.Slice
