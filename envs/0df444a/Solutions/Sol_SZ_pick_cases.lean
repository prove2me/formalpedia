-- Prove2me | solution 1 for SZ.pick_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:53:02.460501+00:00
-- url     : https://prove2.me/submissions/39ecddca-ce6f-479c-93f0-5da544160be6

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
theorem _root_.solution (w : ℝ) :
    (w ≤ 1 + Real.sqrt 3 ∧ pick w = (0, 0)) ∨
    (1 + Real.sqrt 3 < w ∧ w < 2 * Real.sqrt 3 ∧ pick w = (2, 0)) ∨
    (2 * Real.sqrt 3 ≤ w ∧ w ≤ 1 + 3 * Real.sqrt 3 ∧ pick w = (0, 2)) ∨
    (1 + 3 * Real.sqrt 3 < w ∧ pick w = (2, 2)) := by
  unfold pick
  split_ifs with h1 h2 h3
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨not_le.mp h1, h2, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨not_lt.mp h2, h3, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨not_le.mp h3, rfl⟩))
end SZ
