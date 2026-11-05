-- Prove2me | solution 1 for VariableBound.Family.card_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:05:56.373198+00:00
-- url     : https://prove2.me/submissions/a135d805-405d-414c-be27-64561a5c745c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Family_Pairwise
import Definitions.Def_VariableBound_Family_SmallBias
import Definitions.Def_VariableBound_Family_Main
import Theorems.Thm_VariableBound_Family_card_quad
import Theorems.Thm_VariableBound_Family_mem_Gam
import Theorems.Thm_VariableBound_Pairwise_card_H
import Theorems.Thm_VariableBound_SmallBias_half


set_option autoImplicit false
section
section
open VariableBound
open Finset AppVariables VariableBound.Pairwise
open VariableBound.Family
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
namespace VariableBound.Family
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha1 : 1 ≤ a) (ha : a - 1 ≤ s) (E : Fin m) :
    2 ^ a * #{u : F × F × F × F | E ∈ Gam bits ϑ a u} ≤ Fintype.card F ^ 4 := by
  simp_rw [mem_Gam]
  rw [card_quad fun p r => H bits ϑ a p E ∧ ip (bits (r.1 ^ E.val)) (bits r.2) = 1]
  have h1 : ∀ p : F × F, #{r : F × F | H bits ϑ a p E ∧ ip (bits (r.1 ^ E.val)) (bits r.2) = 1}
      = if H bits ϑ a p E then #{r : F × F | ip (bits (r.1 ^ E.val)) (bits r.2) = 1} else 0 := by
    intro p
    by_cases h : H bits ϑ a p E <;> simp [h]
  simp_rw [h1]
  rw [← sum_filter, sum_const, smul_eq_mul]
  calc 2 ^ a * (#{p : F × F | H bits ϑ a p E} * #{r : F × F | ip (bits (r.1 ^ E.val)) (bits r.2) = 1})
      = (2 ^ (a - 1) * #{p : F × F | H bits ϑ a p E}) * (2 * #{r : F × F | ip (bits (r.1 ^ E.val)) (bits r.2) = 1}) := by
        rw [show 2 ^ a = 2 ^ (a - 1) * 2 by rw [← pow_succ, Nat.sub_add_cancel ha1]]
        ring
    _ ≤ Fintype.card F ^ 2 * Fintype.card F ^ 2 := by
        rw [card_H bits ϑ a ha E]
        exact Nat.mul_le_mul_left _ (SmallBias.half bits E)
    _ = Fintype.card F ^ 4 := by ring
end VariableBound.Family
