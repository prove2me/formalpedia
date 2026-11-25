-- Prove2me | solution 1 for SZ.not_isSquare_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:44:09.59715+00:00
-- url     : https://prove2.me/submissions/59db004a-b4d4-40e3-a61e-52e76cbc389a

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
namespace SZ
theorem _root_.solution {n : ℕ} (hn : 0 < n) (h : ∀ r, r ≤ n → r * r ≠ n) :
    ¬ IsSquare n := by
  rintro ⟨r, hr⟩
  have hle : r ≤ n := by
    by_contra hgt
    push Not at hgt
    nlinarith
  exact h r hle hr.symm
end SZ
