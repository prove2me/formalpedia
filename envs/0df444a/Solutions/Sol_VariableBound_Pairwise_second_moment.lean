-- Prove2me | solution 1 for VariableBound.Pairwise.second_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:56:10.167277+00:00
-- url     : https://prove2.me/submissions/eb1fa844-afa5-4b1f-9b9c-6eabc5d40448

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.LinearCombination
import Definitions.Def_VariableBound_Family_Pairwise
import Theorems.Thm_VariableBound_Pairwise_sum_Y
import Theorems.Thm_VariableBound_Pairwise_sum_Y_sq
import Theorems.Thm_VariableBound_Pairwise_cauchy_schwarz

set_option autoImplicit false
section
section
open VariableBound VariableBound.Pairwise
open Finset AppVariables
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
namespace VariableBound.Pairwise
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha1 : 1 ≤ a) (ha : a - 1 ≤ s) (V : Finset (Fin m)) (hV : 2 ^ a < #V) :
    2 * Fintype.card F ^ 2 < 3 * #{p : F × F | ∃ E ∈ V, H bits ϑ a p E} := by
  have hP : #{p : F × F | ∃ E ∈ V, H bits ϑ a p E} = #{p : F × F | 0 < Y bits ϑ a V p} := by
    congr 1
    ext p
    simp [Y, card_pos, Finset.Nonempty]
  rw [hP]
  have hw : 2 ^ a = 2 * 2 ^ (a - 1) := by rw [← pow_succ', Nat.sub_add_cancel ha1]
  have h4 : (4 : ℕ) ^ (a - 1) = 2 ^ (a - 1) * 2 ^ (a - 1) := by rw [← mul_pow]; norm_num
  have hq : 0 < Fintype.card F ^ 2 := pow_pos Fintype.card_pos 2
  have e1 := sum_Y bits ϑ a ha V
  have e2 := sum_Y_sq bits ϑ a ha V
  have e3 := cauchy_schwarz bits ϑ a V
  rw [h4] at e2
  rw [hw] at hV
  generalize (2 : ℕ) ^ (a - 1) = w at *
  generalize Fintype.card F ^ 2 = Q at *
  generalize ∑ p : F × F, Y bits ϑ a V p = S₁ at *
  generalize ∑ p : F × F, Y bits ϑ a V p ^ 2 = S₂ at *
  generalize #{p : F × F | 0 < Y bits ϑ a V p} = P at *
  generalize #V = n at *
  have hn : 0 < n := by omega
  -- n·Q ≤ P·(n + w), which is Pr(Y > 0) ≥ y/(y + 1)
  have h5 : n * Q * (n * Q) ≤ P * (n + w) * (n * Q) :=
    calc n * Q * (n * Q) = w * w * S₁ ^ 2 := by rw [← e1]; ring
      _ ≤ w * w * (P * S₂) := Nat.mul_le_mul_left _ e3
      _ = P * (w * w * S₂) := by ring
      _ ≤ P * ((n ^ 2 + w * n) * Q) := Nat.mul_le_mul_left _ e2
      _ = P * (n + w) * (n * Q) := by ring
  have h6 : n * Q ≤ P * (n + w) := Nat.le_of_mul_le_mul_right h5 (Nat.mul_pos hn hq)
  by_contra hc
  have hc' : 3 * P ≤ 2 * Q := not_lt.1 hc
  have h7 : 3 * n * Q ≤ 2 * (n + w) * Q :=
    calc 3 * n * Q = 3 * (n * Q) := by ring
      _ ≤ 3 * (P * (n + w)) := Nat.mul_le_mul_left _ h6
      _ = 3 * P * (n + w) := by ring
      _ ≤ 2 * Q * (n + w) := Nat.mul_le_mul_right _ hc'
      _ = 2 * (n + w) * Q := by ring
  have h8 := Nat.le_of_mul_le_mul_right h7 hq
  omega
end VariableBound.Pairwise
