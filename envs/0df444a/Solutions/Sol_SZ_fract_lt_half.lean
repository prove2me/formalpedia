-- Prove2me | solution 1 for SZ.fract_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:28:32.90854+00:00
-- url     : https://prove2.me/submissions/3e131572-dd4e-44ef-9137-715ebf09d656

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_SqrtTwo
import Theorems.Thm_SZ_floor_two_mul
import Theorems.Thm_SZ_floor_two_fract_cases

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution {u : ℝ} (h : Even ⌊u⌋) (h2 : Even ⌊2 * u⌋) : Int.fract u < 1 / 2 := by
  have key : ⌊2 * Int.fract u⌋ = 0 := by
    have hsplit := floor_two_mul u
    have hev : Even ⌊2 * Int.fract u⌋ := by
      have : ⌊2 * Int.fract u⌋ = ⌊2 * u⌋ - 2 * ⌊u⌋ := by omega
      rw [this]
      exact h2.sub (h.mul_left 2)
    rcases floor_two_fract_cases u with h0 | h1
    · exact h0
    · rw [h1] at hev; exact absurd hev (by decide)
  have := Int.lt_floor_add_one (2 * Int.fract u)
  rw [key] at this
  push_cast at this
  linarith
end SZ
