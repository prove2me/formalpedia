-- Prove2me | solution 1 for SZ.digitA_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:25:10.470057+00:00
-- url     : https://prove2.me/submissions/f87f09e1-f91f-476d-898c-248654252d30

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_pick_fst_mem

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (k : ℕ) : digitA k = 0 ∨ digitA k = 2 := pick_fst_mem (W k)
end SZ
