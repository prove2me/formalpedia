-- Prove2me | solution 1 for SZ.Slice.bsel_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:43:44.461333+00:00
-- url     : https://prove2.me/submissions/6fdf3840-bf61-4de8-bf1e-17ab773b94c0

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
theorem _root_.solution (w : ℝ) : S.bsel w ≤ S.e := min_le_left _ _
end SZ.Slice
