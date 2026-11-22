-- Prove2me | solution 1 for SZ.union_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:54:38.147178+00:00
-- url     : https://prove2.me/submissions/11b97711-c698-4954-86b3-df972d3b9fd8

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Defs

set_option autoImplicit false
open SZ
open Int
namespace SZ
theorem _root_.solution {α : ℝ} (hα : 1 < α) : α ∈ MahlerZ ∨ α ∈ S := by
  by_cases h : α ∈ MahlerZ
  · exact Or.inl h
  · exact Or.inr ⟨hα, h⟩
end SZ
