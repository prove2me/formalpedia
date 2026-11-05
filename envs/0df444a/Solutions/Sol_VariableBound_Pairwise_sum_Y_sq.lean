-- Prove2me | solution 1 for VariableBound.Pairwise.sum_Y_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:49:33.829208+00:00
-- url     : https://prove2.me/submissions/bb0f57d9-f920-4865-8cb8-9f09579cebb9

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
import Theorems.Thm_VariableBound_Pairwise_card_H
import Theorems.Thm_VariableBound_Pairwise_card_H_and

set_option autoImplicit false
section
section
open VariableBound VariableBound.Pairwise
open Finset AppVariables
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
namespace VariableBound.Pairwise
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha : a - 1 ≤ s) (V : Finset (Fin m)) :
    4 ^ (a - 1) * ∑ p : F × F, Y bits ϑ a V p ^ 2 ≤ (#V ^ 2 + 2 ^ (a - 1) * #V) * Fintype.card F ^ 2 := by
  have h1 : ∀ p : F × F, Y bits ϑ a V p ^ 2 = ∑ E ∈ V, ∑ E' ∈ V, if H bits ϑ a p E ∧ H bits ϑ a p E' then 1 else 0 := by
    intro p
    rw [Y, card_filter, sq, sum_mul_sum]
    refine sum_congr rfl fun E _ => sum_congr rfl fun E' _ => ?_
    by_cases h : H bits ϑ a p E <;> by_cases h' : H bits ϑ a p E' <;> simp [h, h']
  have h2 : ∀ E E' : Fin m, 4 ^ (a - 1) * ∑ p : F × F, (if H bits ϑ a p E ∧ H bits ϑ a p E' then 1 else 0)
      ≤ Fintype.card F ^ 2 + if E = E' then 2 ^ (a - 1) * Fintype.card F ^ 2 else 0 := by
    intro E E'
    rw [← card_filter]
    by_cases h : E = E'
    · subst h
      simp only [and_self, if_true]
      rw [← card_H bits ϑ a ha E, show (4 : ℕ) = 2 * 2 by norm_num, mul_pow, mul_assoc]
      exact Nat.le_add_left _ _
    · rw [card_H_and bits ϑ a ha E E' h, if_neg h]
      exact Nat.le_add_right _ _
  simp_rw [h1]
  rw [sum_comm, mul_sum]
  calc ∑ E ∈ V, 4 ^ (a - 1) * ∑ p : F × F, ∑ E' ∈ V, (if H bits ϑ a p E ∧ H bits ϑ a p E' then 1 else 0)
      = ∑ E ∈ V, ∑ E' ∈ V, 4 ^ (a - 1) * ∑ p : F × F, (if H bits ϑ a p E ∧ H bits ϑ a p E' then 1 else 0) := by
        refine sum_congr rfl fun E _ => ?_
        rw [sum_comm, mul_sum]
    _ ≤ ∑ E ∈ V, ∑ E' ∈ V, (Fintype.card F ^ 2 + if E = E' then 2 ^ (a - 1) * Fintype.card F ^ 2 else 0) :=
        sum_le_sum fun E _ => sum_le_sum fun E' _ => h2 E E'
    _ = ∑ E ∈ V, (#V * Fintype.card F ^ 2 + 2 ^ (a - 1) * Fintype.card F ^ 2) := by
        refine sum_congr rfl fun E hE => ?_
        rw [sum_add_distrib, sum_const, smul_eq_mul, sum_ite_eq, if_pos hE]
    _ = (#V ^ 2 + 2 ^ (a - 1) * #V) * Fintype.card F ^ 2 := by
        rw [sum_const, smul_eq_mul]
        ring
end VariableBound.Pairwise
