-- Prove2me | solution 1 for SZ.Slice.irrational_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:39:32.820584+00:00
-- url     : https://prove2.me/submissions/a0b4c581-b69a-496d-99e3-3086dda73b88

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
theorem _root_.solution : Irrational S.sq :=
  irrational_sqrt_natCast_iff.mpr S.not_square
end SZ.Slice
