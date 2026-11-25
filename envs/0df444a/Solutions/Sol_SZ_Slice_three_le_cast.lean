-- Prove2me | solution 1 for SZ.Slice.three_le_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:43:30.124809+00:00
-- url     : https://prove2.me/submissions/151b0349-5c21-48db-af77-ad248987f383

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
theorem _root_.solution : (3 : ℝ) ≤ (S.m : ℝ) := by exact_mod_cast S.three_le
end SZ.Slice
