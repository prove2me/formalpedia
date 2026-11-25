-- Prove2me | solution 1 for SZ.W_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:37:23.260653+00:00
-- url     : https://prove2.me/submissions/4a7d2db3-e14f-4ab4-9851-4615d242fcf6

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_W_ne_val

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (k : ℕ) : W k ≠ 0 := by
  have h := W_ne_val k (p := 0) (q := 0) (by norm_num)
  simpa using h
end SZ
