-- Prove2me | solution 1 for SZ.digitB_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:42.138246+00:00
-- url     : https://prove2.me/submissions/e801e885-dba9-4153-adbd-71812ca63532

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_digitB_mem

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (k : ℕ) : Even (digitB k) := by
  rcases digitB_mem k with h | h <;> rw [h] <;> decide
end SZ
