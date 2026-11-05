-- Prove2me | solution 1 for VariableBound.Pairwise.cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:49:03.36695+00:00
-- url     : https://prove2.me/submissions/a6fecd11-ee1b-4dce-b373-f3f262113a62

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

set_option autoImplicit false
section
section
open VariableBound VariableBound.Pairwise
open Finset AppVariables
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
omit [DecidableEq F]
namespace VariableBound.Pairwise
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (V : Finset (Fin m)) :
    (∑ p : F × F, Y bits ϑ a V p) ^ 2 ≤ #{p : F × F | 0 < Y bits ϑ a V p} * ∑ p : F × F, Y bits ϑ a V p ^ 2 := by
  have h := sum_mul_sq_le_sq_mul_sq (univ : Finset (F × F)) (fun p => if 0 < Y bits ϑ a V p then 1 else 0) (Y bits ϑ a V)
  have h1 : ∀ p : F × F, (if 0 < Y bits ϑ a V p then 1 else 0) * Y bits ϑ a V p = Y bits ϑ a V p := by
    intro p
    rcases Nat.eq_zero_or_pos (Y bits ϑ a V p) with h0 | h0 <;> simp [h0]
  have h2 : ∀ p : F × F, (if 0 < Y bits ϑ a V p then 1 else 0) ^ 2 = if 0 < Y bits ϑ a V p then 1 else 0 := by
    intro p
    split_ifs <;> simp
  simp_rw [h1, h2] at h
  rwa [← card_filter] at h
end VariableBound.Pairwise
