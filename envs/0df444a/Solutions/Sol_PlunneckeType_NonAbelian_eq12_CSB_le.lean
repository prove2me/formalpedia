-- Prove2me | solution 1 for PlunneckeType.NonAbelian.eq12_CSB_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:24:36.512742+00:00
-- url     : https://prove2.me/submissions/4832690a-53f9-4e63-99b9-baa36a0c6d06

import Mathlib
set_option autoImplicit false
open scoped Pointwise
open Finset

theorem solution {G : Type*} [Group G] [DecidableEq G] (A B S : Finset G) (α : ℝ)
    (h1 : (#(A * B) : ℝ) ≤ α * #A)
    (hSA : S ⊆ A) (hS : S.Nonempty)
    (hmin : ∀ Z ⊆ A, Z.Nonempty → (#(S * B) : ℝ) * #Z ≤ #(Z * B) * #S) :
    ∀ C : Finset G, (#(C * S * B) : ℝ) ≤ α * #(C * S) := by
  intro C
  have hApos : 0 < (#A : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (hS.mono hSA)
  have hSpos : 0 < (#S : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  -- |SB| ≤ α |S|
  have hSB : (#(S * B) : ℝ) ≤ α * #S := by
    have h2 := hmin A subset_rfl (hS.mono hSA)
    have h3 : (#(S * B) : ℝ) * #A ≤ (α * #S) * #A := by nlinarith [Nat.cast_nonneg (α := ℝ) #S]
    exact le_of_mul_le_mul_right h3 hApos
  have hA' : ∀ A' ⊆ S, #(S * B) * #A' ≤ #(A' * B) * #S := by
    intro A' hA'S
    rcases A'.eq_empty_or_nonempty with rfl | hne
    · simp
    · have := hmin A' (hA'S.trans hSA) hne
      exact_mod_cast this
  have pp := Finset.pluennecke_petridis_inequality_mul (A := S) (B := B) C hA'
  have pp' : (#(C * S * B) : ℝ) * #S ≤ #(S * B) * #(C * S) := by exact_mod_cast pp
  have h4 : (#(C * S * B) : ℝ) * #S ≤ (α * #(C * S)) * #S := by
    calc (#(C * S * B) : ℝ) * #S ≤ #(S * B) * #(C * S) := pp'
      _ ≤ (α * #S) * #(C * S) := mul_le_mul_of_nonneg_right hSB (Nat.cast_nonneg _)
      _ = (α * #(C * S)) * #S := by ring
  exact le_of_mul_le_mul_right h4 hSpos
