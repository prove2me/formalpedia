-- Prove2me | solution 1 for SZ.floor_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:27:21.574934+00:00
-- url     : https://prove2.me/submissions/bb47167a-f9e7-46bc-a219-c164eaf131d5

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_SqrtTwo

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution (u : ℝ) : ⌊2 * u⌋ = 2 * ⌊u⌋ + ⌊2 * Int.fract u⌋ := by
  have e : (2 : ℝ) * u = 2 * Int.fract u + ((2 * ⌊u⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [e, Int.floor_add_intCast]
  ring
end SZ
