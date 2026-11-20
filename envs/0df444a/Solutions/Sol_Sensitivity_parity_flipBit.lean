-- Prove2me | solution 1 for Sensitivity.parity_flipBit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:59:38.18435+00:00
-- url     : https://prove2.me/submissions/84801b02-4715-4437-826c-1aff3cbf2c39

import Definitions.Def_Sensitivity_Defs
import Definitions.Def_Sensitivity_Multilinear
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_Sensitivity_Parity
import Theorems.Thm_Sensitivity_boolToInt_false
import Theorems.Thm_Sensitivity_boolToInt_true
import Theorems.Thm_Sensitivity_flipBit_apply_ne
import Theorems.Thm_Sensitivity_flipBit_apply_same
import Theorems.Thm_Sensitivity_flipBit_flipBit_same
import Theorems.Thm_Sensitivity_indicator_mem
import Theorems.Thm_Sensitivity_indicator_not_mem
attribute [local simp] Sensitivity.boolToInt_false
attribute [local simp] Sensitivity.boolToInt_true
attribute [local simp] Sensitivity.flipBit_apply_ne
attribute [local simp] Sensitivity.flipBit_apply_same
attribute [local simp] Sensitivity.flipBit_flipBit_same
attribute [local simp] Sensitivity.indicator_mem
attribute [local simp] Sensitivity.indicator_not_mem



set_option autoImplicit false
open Sensitivity
variable {n : ℕ}
namespace Sensitivity
theorem _root_.solution (x : Fin n → Bool) (i : Fin n) :
    parity (flipBit x i) = -parity x := by
  unfold parity
  have key : ∀ (a b : ℕ), a + 1 = b ∨ b + 1 = a →
      (-1 : ℤ) ^ a = -((-1 : ℤ) ^ b) := by
    intro a b hab
    rcases hab with ⟨rfl⟩ | ⟨rfl⟩ <;> simp [pow_succ]
  apply key
  cases hxi : x i
  · right
    have hS : Finset.univ.filter (fun j : Fin n => flipBit x i j) =
              insert i (Finset.univ.filter (fun j : Fin n => x j)) := by
      ext j; simp [flipBit]; by_cases h : j = i <;> simp [h, hxi, Function.update]
    have hni : i ∉ Finset.univ.filter (fun j : Fin n => x j) := by simp [hxi]
    rw [hS, Finset.card_insert_of_notMem hni]
  · left
    have hS : Finset.univ.filter (fun j : Fin n => flipBit x i j) =
              (Finset.univ.filter (fun j : Fin n => x j)).erase i := by
      ext j; simp [flipBit]; by_cases h : j = i <;> simp [h, hxi, Function.update]
    have hi : i ∈ Finset.univ.filter (fun j : Fin n => x j) := by simp [hxi]
    rw [hS, Finset.card_erase_of_mem hi]
    have hpos := Finset.card_pos.mpr ⟨i, hi⟩
    omega
end Sensitivity
