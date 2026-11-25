-- Prove2me | solution 1 for SZ.Slice.w0_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:26:21.242823+00:00
-- url     : https://prove2.me/submissions/f4661d6b-e041-4990-bb14-32aebac3208b

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
variable {S}
namespace SZ.Slice
theorem _root_.solution (S : Slice) (j k₀ : ℤ) : S.w0 j k₀ = (S.m : ℝ) * S.sigma j k₀ := rfl
end SZ.Slice
