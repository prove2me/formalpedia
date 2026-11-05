-- Prove2me | solution 1 for Sherbrooke.lowerHull_le_and_convex
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-04T12:26:27.937388+00:00
-- url     : https://prove2.me/submissions/4279a83f-e3a2-4c47-8cc3-887952cd4095

import Definitions.Def_Sherbrooke_lowerHull
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Set Sherbrooke

theorem solution (Ξ : ℕ → ℝ) (hbdd : BddBelow (Set.range Ξ)) :
    (∀ m : ℕ, lowerHull Ξ m ≤ Ξ m) ∧
      ∀ m : ℕ, lowerHull Ξ (m + 1) - lowerHull Ξ m ≤
        lowerHull Ξ (m + 2) - lowerHull Ξ (m + 1) := by
  let S (m : ℕ) := {y : ℝ | ∃ a b : ℝ, (∀ k : ℕ, a * (k : ℝ) + b ≤ Ξ k) ∧ y = a * (m : ℝ) + b}
  obtain ⟨l, hl⟩ := hbdd
  have hS : ∀ m, (S m).Nonempty := by
    intro m
    exact ⟨l, 0, l, (by intro k; simpa using hl (mem_range_self k)), by simp⟩
  have hB : ∀ m, BddAbove (S m) := by
    intro m
    refine ⟨Ξ m, ?_⟩
    rintro t ⟨a, b, hab, rfl⟩
    exact hab m
  have hle : ∀ m, lowerHull Ξ m ≤ Ξ m := by
    intro m
    apply csSup_le (hS m)
    rintro t ⟨a, b, hab, rfl⟩
    exact hab m
  refine ⟨hle, ?_⟩
  intro m
  have hmid : lowerHull Ξ (m + 1) ≤ (lowerHull Ξ m + lowerHull Ξ (m + 2)) / 2 := by
    apply csSup_le (hS (m + 1))
    rintro t ⟨a, b, hab, rfl⟩
    have hl : a * (m : ℝ) + b ≤ lowerHull Ξ m := le_csSup (hB m) ⟨a, b, hab, rfl⟩
    have hr : a * ((m + 2 : ℕ) : ℝ) + b ≤ lowerHull Ξ (m + 2) :=
      le_csSup (hB (m + 2)) ⟨a, b, hab, rfl⟩
    push_cast at *
    linarith
  linarith

#print axioms solution
