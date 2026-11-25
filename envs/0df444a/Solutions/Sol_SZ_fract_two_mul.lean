-- Prove2me | solution 1 for SZ.fract_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:27:43.342538+00:00
-- url     : https://prove2.me/submissions/61df3ec2-f655-4bee-97bd-9c950f09d744

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_SqrtTwo

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution {u : ℝ} (h : Int.fract u < 1 / 2) :
    Int.fract (2 * u) = 2 * Int.fract u := by
  have e : (2 : ℝ) * u = ((2 * ⌊u⌋ : ℤ) : ℝ) + 2 * Int.fract u := by
    rw [Int.fract]; push_cast; ring
  rw [e, Int.fract_intCast_add]
  refine Int.fract_eq_self.mpr ⟨?_, ?_⟩
  · have := Int.fract_nonneg u; linarith
  · linarith
end SZ
