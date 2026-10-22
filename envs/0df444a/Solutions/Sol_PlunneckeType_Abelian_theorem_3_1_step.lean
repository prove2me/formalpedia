-- Prove2me | solution 1 for PlunneckeType.Abelian.theorem_3_1_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:17:33.093193+00:00
-- url     : https://prove2.me/submissions/07c7c24c-1b6a-4557-8247-d77320690692

import Mathlib
set_option autoImplicit false
open scoped Pointwise
open Finset

theorem solution {G : Type*} [AddCommGroup G] [DecidableEq G] (A B X : Finset G) (α : ℝ)
    (hAB : (#(A + B) : ℝ) ≤ α * #A)
    (hXA : X ⊆ A) (hX : X.Nonempty)
    (hmin : ∀ Z ⊆ A, Z.Nonempty → (#(X + B) : ℝ) * #Z ≤ #(Z + B) * #X)
    (h : ℕ) (hh : 1 ≤ h) :
    (#(X + h • B) : ℝ) ≤ α * #(X + (h - 1) • B) := by
  have hApos : 0 < (#A : ℝ) := by exact_mod_cast Finset.card_pos.mpr (hX.mono hXA)
  have hXpos : 0 < (#X : ℝ) := by exact_mod_cast Finset.card_pos.mpr hX
  have hXB : (#(X + B) : ℝ) ≤ α * #X := by
    have h2 := hmin A subset_rfl (hX.mono hXA)
    have h3 : (#(X + B) : ℝ) * #A ≤ (α * #X) * #A := by
      calc (#(X + B) : ℝ) * #A ≤ #(A + B) * #X := h2
        _ ≤ (α * #A) * #X := mul_le_mul_of_nonneg_right hAB (Nat.cast_nonneg _)
        _ = (α * #X) * #A := by ring
    exact le_of_mul_le_mul_right h3 hApos
  have hA' : ∀ A' ⊆ X, #(X + B) * #A' ≤ #(A' + B) * #X := by
    intro A' hA'X
    rcases A'.eq_empty_or_nonempty with rfl | hne
    · simp
    · have := hmin A' (hA'X.trans hXA) hne
      exact_mod_cast this
  have pp := Finset.pluennecke_petridis_inequality_add (A := X) (B := B) ((h - 1) • B) hA'
  have pp' : (#((h - 1) • B + X + B) : ℝ) * #X ≤ #(X + B) * #((h - 1) • B + X) := by
    exact_mod_cast pp
  have e1 : (h - 1) • B + X + B = X + h • B := by
    have : h • B = (h - 1) • B + B := by
      rw [← succ_nsmul]; congr 1; omega
    rw [this, add_comm ((h - 1) • B) X, add_assoc]
  have e2 : (h - 1) • B + X = X + (h - 1) • B := add_comm _ _
  rw [e1, e2] at pp'
  have h4 : (#(X + h • B) : ℝ) * #X ≤ (α * #(X + (h - 1) • B)) * #X := by
    calc (#(X + h • B) : ℝ) * #X ≤ #(X + B) * #(X + (h - 1) • B) := pp'
      _ ≤ (α * #X) * #(X + (h - 1) • B) := mul_le_mul_of_nonneg_right hXB (Nat.cast_nonneg _)
      _ = (α * #(X + (h - 1) • B)) * #X := by ring
  exact le_of_mul_le_mul_right h4 hXpos
