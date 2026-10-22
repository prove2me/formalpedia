-- Prove2me | solution 1 for PlunneckeType.Tao.eq6_BAB_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:26:08.36369+00:00
-- url     : https://prove2.me/submissions/1e6b77d9-1d3c-45d0-ae36-88911148b02b

import Mathlib
set_option autoImplicit false
open scoped Pointwise
open Finset

theorem solution {G : Type*} [Group G] [DecidableEq G] (A B : Finset G) (α : ℝ)
    (hBB : (#(B * B) : ℝ) ≤ α * #B)
    (hAB : A ⊆ B) (hA : A.Nonempty)
    (hmin : ∀ Z ⊆ B, Z.Nonempty → (#(A * B) : ℝ) * #Z ≤ #(Z * B) * #A) :
    (#(B * A * B) : ℝ) ≤ α ^ 2 * #B := by
  have hApos : 0 < (#A : ℝ) := by exact_mod_cast Finset.card_pos.mpr hA
  have hBpos : 0 < (#B : ℝ) := by exact_mod_cast Finset.card_pos.mpr (hA.mono hAB)
  -- |AB| ≤ α |A|
  have hAB' : (#(A * B) : ℝ) ≤ α * #A := by
    have h2 := hmin B subset_rfl (hA.mono hAB)
    have h3 : (#(A * B) : ℝ) * #B ≤ (α * #A) * #B := by
      calc (#(A * B) : ℝ) * #B ≤ #(B * B) * #A := h2
        _ ≤ (α * #B) * #A := mul_le_mul_of_nonneg_right hBB (Nat.cast_nonneg _)
        _ = (α * #A) * #B := by ring
    exact le_of_mul_le_mul_right h3 hBpos
  -- |BA| ≤ α |B|
  have hBA : (#(B * A) : ℝ) ≤ α * #B := by
    have : #(B * A) ≤ #(B * B) := Finset.card_le_card (Finset.mul_subset_mul_left hAB)
    exact (Nat.cast_le.mpr this).trans hBB
  have hA' : ∀ A' ⊆ A, #(A * B) * #A' ≤ #(A' * B) * #A := by
    intro A' hA'A
    rcases A'.eq_empty_or_nonempty with rfl | hne
    · simp
    · have := hmin A' (hA'A.trans hAB) hne
      exact_mod_cast this
  have pp := Finset.pluennecke_petridis_inequality_mul (A := A) (B := B) B hA'
  have pp' : (#(B * A * B) : ℝ) * #A ≤ #(A * B) * #(B * A) := by exact_mod_cast pp
  have hαnn : 0 ≤ α * #A := le_trans (Nat.cast_nonneg _) hAB'
  have h4 : (#(B * A * B) : ℝ) * #A ≤ (α ^ 2 * #B) * #A := by
    calc (#(B * A * B) : ℝ) * #A ≤ #(A * B) * #(B * A) := pp'
      _ ≤ (α * #A) * (α * #B) :=
          mul_le_mul hAB' hBA (Nat.cast_nonneg _) hαnn
      _ = (α ^ 2 * #B) * #A := by ring
  exact le_of_mul_le_mul_right h4 hApos
