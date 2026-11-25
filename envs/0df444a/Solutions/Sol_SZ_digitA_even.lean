-- Prove2me | solution 1 for SZ.digitA_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:28:01.801803+00:00
-- url     : https://prove2.me/submissions/71772405-b04f-46e1-a714-9268fea0e7cc

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_digitA_mem

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (k : ℕ) : Even (digitA k) := by
  rcases digitA_mem k with h | h <;> rw [h] <;> decide
end SZ
