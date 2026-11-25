-- Prove2me | solution 1 for SZ.W_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:47:55.994006+00:00
-- url     : https://prove2.me/submissions/8f83a077-92f9-4b10-bd9b-38512b608944

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_W_mem
import Theorems.Thm_SZ_W_ne_zero

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (k : ℕ) : 0 < W k := lt_of_le_of_ne (W_mem k).1 (Ne.symm (W_ne_zero k))
end SZ
