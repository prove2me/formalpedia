-- Prove2me | solution 1 for SZ.pick_eq_00
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:21:31.411435+00:00
-- url     : https://prove2.me/submissions/278cd9ce-5d05-4c5a-a306-6ed3b5acab73

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
theorem _root_.solution {w : ℝ} (h : w ≤ 1 + Real.sqrt 3) : pick w = (0, 0) := by
  unfold pick; rw [if_pos h]
end SZ
