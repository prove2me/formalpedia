-- Prove2me | solution 1 for VariableBound.Pairwise.sum_Y
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:48:51.672065+00:00
-- url     : https://prove2.me/submissions/61541031-94fe-4f4c-95a0-1f49b47f0d16

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

set_option autoImplicit false
section
section
open VariableBound VariableBound.Pairwise
open Finset AppVariables
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
namespace VariableBound.Pairwise
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha : a - 1 ≤ s) (V : Finset (Fin m)) :
    2 ^ (a - 1) * ∑ p : F × F, Y bits ϑ a V p = #V * Fintype.card F ^ 2 := by
  simp_rw [Y, card_filter]
  rw [sum_comm, mul_sum]
  have h : ∀ E ∈ V, 2 ^ (a - 1) * ∑ p : F × F, (if H bits ϑ a p E then 1 else 0) = Fintype.card F ^ 2 := by
    intro E _
    rw [← card_filter]
    exact card_H bits ϑ a ha E
  rw [sum_congr rfl h, sum_const, smul_eq_mul]
end VariableBound.Pairwise
