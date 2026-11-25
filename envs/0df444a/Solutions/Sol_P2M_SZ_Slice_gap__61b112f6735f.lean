-- Prove2me | solution 1 for P2M_SZ_Slice_gap__61b112f6735f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:23:51.898523+00:00
-- url     : https://prove2.me/submissions/26d4ac3a-d8b0-4946-85c7-ebecbde77b7e

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
theorem _root_.solution : (S.p : ℝ) * S.sq - (S.e : ℝ) ≤ S.U := S.gap
end SZ.Slice
