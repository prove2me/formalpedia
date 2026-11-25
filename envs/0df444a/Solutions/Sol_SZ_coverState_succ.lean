-- Prove2me | solution 1 for SZ.coverState_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:05:17.850216+00:00
-- url     : https://prove2.me/submissions/208600ff-9cec-47f7-9bbb-2cf1a7bbd20f

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (k : ℕ) :
    coverState (k + 1) = (3 * ((coverState k).1 - digitA k), 3 * ((coverState k).2 - digitB k)) :=
  rfl
end SZ
