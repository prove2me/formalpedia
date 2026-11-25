-- Prove2me | solution 1 for SZ.Slice.dB_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:48:57.155888+00:00
-- url     : https://prove2.me/submissions/e6630f8b-f7e3-49fa-8515-a8507e455d58

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
theorem _root_.solution (w₀ : ℝ) (k : ℕ) : S.dB w₀ k = S.bsel (S.W w₀ k) := rfl
end SZ.Slice
