-- Prove2me | solution 1 for SZ.W_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:09:08.718459+00:00
-- url     : https://prove2.me/submissions/30cc0cfd-16bd-4f96-8868-5432ab7056d3

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_coverState_succ

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (k : ℕ) :
    W (k + 1) = 3 * (W k - ((digitA k : ℝ) + (digitB k : ℝ) * Real.sqrt 3)) := by
  rw [W, coverState_succ, W]
  push_cast
  ring
end SZ
