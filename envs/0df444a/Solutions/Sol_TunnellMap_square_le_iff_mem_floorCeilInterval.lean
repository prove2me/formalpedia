-- Prove2me | solution 1 for TunnellMap.square_le_iff_mem_floorCeilInterval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:50:20.804725+00:00
-- url     : https://prove2.me/submissions/2f0a7935-1b7c-4aab-ad08-2d9722b092fe

import Definitions.Def_TunnellMap_AffineLattice
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Data.Rat.Floor
import Definitions.Def_TunnellMap_ShortInterval
import Theorems.Thm_TunnellMap_dot_tau
import Theorems.Thm_TunnellMap_evenEquiv_apply
import Theorems.Thm_TunnellMap_evenEquiv_symm_apply
import Theorems.Thm_TunnellMap_qForm_aLift
import Theorems.Thm_TunnellMap_qForm_bLift
import Theorems.Thm_TunnellMap_qForm_tau
attribute [local simp] TunnellMap.dot_tau
attribute [local simp] TunnellMap.evenEquiv_apply
attribute [local simp] TunnellMap.evenEquiv_symm_apply
attribute [local simp] TunnellMap.qForm_aLift
attribute [local simp] TunnellMap.qForm_bLift
attribute [local simp] TunnellMap.qForm_tau



set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n c X b : ℤ}
    (hn : 0 < n) (hX : 0 ≤ X) :
    (n * b - c) ^ 2 ≤ X ↔
      ⌈((c - Int.sqrt X : ℤ) : ℚ) / (n : ℚ)⌉ ≤ b ∧
        b ≤ ⌊((c + Int.sqrt X : ℤ) : ℚ) / (n : ℚ)⌋ := by
  rw [← Int.abs_le_sqrt_iff_sq_le hX, abs_le]
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  constructor
  · rintro ⟨hlower, hupper⟩
    constructor
    · rw [Int.ceil_le]
      apply (div_le_iff₀ hnq).2
      have h : c - Int.sqrt X ≤ n * b := by omega
      exact_mod_cast (show c - Int.sqrt X ≤ b * n by simpa [mul_comm] using h)
    · rw [Int.le_floor]
      apply (le_div_iff₀ hnq).2
      have h : n * b ≤ c + Int.sqrt X := by omega
      exact_mod_cast (show b * n ≤ c + Int.sqrt X by simpa [mul_comm] using h)
  · rintro ⟨hlower, hupper⟩
    rw [Int.ceil_le] at hlower
    rw [Int.le_floor] at hupper
    have hlower' := (div_le_iff₀ hnq).1 hlower
    have hupper' := (le_div_iff₀ hnq).1 hupper
    have hlowerInt : c - Int.sqrt X ≤ b * n := by exact_mod_cast hlower'
    have hupperInt : b * n ≤ c + Int.sqrt X := by exact_mod_cast hupper'
    have hlowerInt' : c - Int.sqrt X ≤ n * b := by
      simpa [mul_comm] using hlowerInt
    have hupperInt' : n * b ≤ c + Int.sqrt X := by
      simpa [mul_comm] using hupperInt
    constructor <;> omega
end TunnellMap
