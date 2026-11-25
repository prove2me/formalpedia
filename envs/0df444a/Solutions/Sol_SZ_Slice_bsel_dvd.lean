-- Prove2me | solution 1 for SZ.Slice.bsel_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:24:57.646511+00:00
-- url     : https://prove2.me/submissions/f11d5bb5-f5d7-48cb-b586-3415ba0b6963

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
theorem _root_.solution (w : ℝ) : S.p ∣ S.bsel w := by
  rcases min_cases S.e (S.p * ⌊w / ((S.p : ℝ) * S.sq)⌋) with ⟨h, -⟩ | ⟨h, -⟩ <;>
    rw [bsel, h]
  · exact S.p_dvd_e
  · exact dvd_mul_right _ _
end SZ.Slice
