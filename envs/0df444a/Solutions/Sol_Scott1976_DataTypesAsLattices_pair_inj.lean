-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.pair_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:57:49.372563+00:00
-- url     : https://prove2.me/submissions/150bf071-6946-4925-bcf8-a169af958297

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Definitions.Def_Scott1976_DataTypesAsLattices_Pomega
import Theorems.Thm_Scott1976_DataTypesAsLattices_triangle_le_of_le
import Theorems.Thm_Scott1976_DataTypesAsLattices_triangle_le_pair

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {n₁ m₁ n₂ m₂ : ℕ} (h : pair n₁ m₁ = pair n₂ m₂) :
    n₁ = n₂ ∧ m₁ = m₂ := by
  have h1 := triangle_le_pair n₁ m₁
  have h2 := triangle_le_pair n₂ m₂
  have hw : n₁ + m₁ = n₂ + m₂ := by
    rcases lt_trichotomy (n₁ + m₁) (n₂ + m₂) with hlt | heq | hgt
    · have hle : triangle (n₁ + m₁ + 1) ≤ triangle (n₂ + m₂) :=
        triangle_le_of_le (Nat.succ_le_of_lt hlt)
      have : pair n₁ m₁ < pair n₁ m₁ :=
        calc
          pair n₁ m₁ < triangle (n₁ + m₁ + 1) := h1.2
          _ ≤ triangle (n₂ + m₂) := hle
          _ ≤ pair n₂ m₂ := h2.1
          _ = pair n₁ m₁ := h.symm
      exact (lt_irrefl _ this).elim
    · exact heq
    · have hle : triangle (n₂ + m₂ + 1) ≤ triangle (n₁ + m₁) :=
        triangle_le_of_le (Nat.succ_le_of_lt hgt)
      have : pair n₂ m₂ < pair n₂ m₂ :=
        calc
          pair n₂ m₂ < triangle (n₂ + m₂ + 1) := h2.2
          _ ≤ triangle (n₁ + m₁) := hle
          _ ≤ pair n₁ m₁ := h1.1
          _ = pair n₂ m₂ := h
      exact (lt_irrefl _ this).elim
  have hm : m₁ = m₂ := by
    have : triangle (n₁ + m₁) + m₁ = triangle (n₂ + m₂) + m₂ := h
    rw [hw] at this
    exact Nat.add_left_cancel this
  have hn : n₁ = n₂ := Nat.add_right_cancel (hw.trans (by rw [hm]))
  exact ⟨hn, hm⟩
end Scott1976.DataTypesAsLattices
