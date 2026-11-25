-- Prove2me | solution 1 for SZ.Slice.one_lt_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:15:07.03643+00:00
-- url     : https://prove2.me/submissions/e2e4f5f4-93b8-4a92-857d-4d540a2ee267

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
theorem _root_.solution : 1 < S.sq := by
  have h1 : (1 : ℝ) < (S.m : ℝ) := by
    have := S.three_le
    have : (3 : ℝ) ≤ (S.m : ℝ) := by exact_mod_cast this
    linarith
  have h : Real.sqrt 1 < Real.sqrt S.m := Real.sqrt_lt_sqrt (by norm_num) h1
  rwa [Real.sqrt_one] at h
end SZ.Slice
