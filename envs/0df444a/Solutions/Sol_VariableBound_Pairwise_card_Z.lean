-- Prove2me | solution 1 for VariableBound.Pairwise.card_Z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:26:55.993417+00:00
-- url     : https://prove2.me/submissions/75c6b10c-bb87-4f89-98a5-5914e04f9eee

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
import Theorems.Thm_VariableBound_Pairwise_card_F

set_option autoImplicit false
section
section
open VariableBound VariableBound.Pairwise
open Finset AppVariables
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}
omit [DecidableEq F]
namespace VariableBound.Pairwise
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (a : ℕ) (ha : a - 1 ≤ s) : 2 ^ (a - 1) * #(Z bits a) = Fintype.card F := by
  have h1 : #(Z bits a) = #(Fintype.piFinset fun i : Fin s => if i.val < a - 1 then ({0} : Finset (ZMod 2)) else univ) := by
    refine card_equiv bits.toEquiv fun x => ?_
    simp only [Z, mem_filter, mem_univ, true_and, Fintype.mem_piFinset, LinearEquiv.coe_toEquiv]
    refine forall_congr' fun i => ?_
    by_cases h : i.val < a - 1 <;> simp [h]
  have h2 : (2 : ℕ) ^ (a - 1) = ∏ i : Fin s, if i.val < a - 1 then 2 else 1 := by
    rw [prod_ite, prod_const, prod_const_one, mul_one, Fin.card_filter_val_lt, min_eq_right ha]
  rw [h1, Fintype.card_piFinset, h2, ← prod_mul_distrib, card_F bits]
  have : ∀ i : Fin s, ((if i.val < a - 1 then 2 else 1) * #(if i.val < a - 1 then ({0} : Finset (ZMod 2)) else univ)) = 2 := by
    intro i
    by_cases h : i.val < a - 1 <;> simp [h, ZMod.card]
  simp [this]
end VariableBound.Pairwise
