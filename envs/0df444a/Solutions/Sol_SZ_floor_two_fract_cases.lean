-- Prove2me | solution 1 for SZ.floor_two_fract_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:27:39.476751+00:00
-- url     : https://prove2.me/submissions/0b6052d3-fc25-4aa8-9ffd-2877df943003

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_SqrtTwo

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution (u : ℝ) : ⌊2 * Int.fract u⌋ = 0 ∨ ⌊2 * Int.fract u⌋ = 1 := by
  have h0 : (0 : ℝ) ≤ 2 * Int.fract u := by
    have := Int.fract_nonneg u; linarith
  have h1 : 2 * Int.fract u < 2 := by
    have := Int.fract_lt_one u; linarith
  have hlo : (0 : ℤ) ≤ ⌊2 * Int.fract u⌋ := Int.floor_nonneg.mpr h0
  have hhi : ⌊2 * Int.fract u⌋ < 2 := by
    have : ((2 : ℤ) : ℝ) = (2 : ℝ) := by norm_num
    exact Int.floor_lt.mpr (by rw [this]; exact h1)
  omega
end SZ
