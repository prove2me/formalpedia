-- Prove2me | solution 1 for SZ.pick_fst_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:21:36.346354+00:00
-- url     : https://prove2.me/submissions/ba19d159-2492-4771-8d58-449dfd06b0a7

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_pick_cases

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (w : ℝ) : (pick w).1 = 0 ∨ (pick w).1 = 2 := by
  rcases pick_cases w with ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩ <;> rw [hp] <;> simp
end SZ
