-- Prove2me | solution 1 for RobersonCx.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @세리나
-- created : 2026-11-26T16:27:02.609315+00:00
-- url     : https://prove2.me/submissions/0e1475ea-8223-40ee-ad95-dd83686407ba

import Mathlib.Data.Nat.ModEq
import Definitions.Def_RobersonCx_InCl

set_option autoImplicit false

open RobersonCx

theorem solution {W : Type} [Finite W] (H : SimpleGraph W) (S : Set ℕ) (hS : S.Infinite)
    (hpos : ∀ m ∈ S, 0 < m) (𝓕 : GraphClass)
    (hF : ∀ m ∈ S, ∃ (V : Type) (_ : Finite V) (F : SimpleGraph V), 𝓕 V F ∧
      ∀ (X : Type) [Finite X] (GX : SimpleGraph X), homCount F GX ≡ homCount H GX [MOD m]) :
    InCl 𝓕 H := by
  unfold InCl
  intro X Y _ _ GX GY hXY
  obtain ⟨m, hm, hlarge⟩ := hS.exists_gt (max (homCount H GX) (homCount H GY))
  obtain ⟨V, hV, F, hmem, hmod⟩ := hF m hm
  letI : Finite V := hV
  have hsame : homCount F GX = homCount F GY := hXY V F hmem
  have hcongr : homCount H GX ≡ homCount H GY [MOD m] := by
    calc
      homCount H GX ≡ homCount F GX [MOD m] := (hmod X GX).symm
      _ ≡ homCount F GY [MOD m] := by rw [hsame]
      _ ≡ homCount H GY [MOD m] := hmod Y GY
  exact hcongr.eq_of_lt_of_lt
    (lt_of_le_of_lt (le_max_left _ _) hlarge)
    (lt_of_le_of_lt (le_max_right _ _) hlarge)
