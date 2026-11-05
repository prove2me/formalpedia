-- Prove2me | solution 1 for VariableBound.StepChoice.Xsum_nil_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:32:06.675483+00:00
-- url     : https://prove2.me/submissions/aaef97eb-635c-4efa-bb34-0b3a335a6fd2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.List
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_StepChoice

set_option autoImplicit false
section
section
open VariableBound VariableBound.StepChoice
open AppVariables Finset
variable {X E ι : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace VariableBound.StepChoice
theorem _root_.solution (V : X → Finset E) (nb n : ℕ) (hX : Fintype.card X ≤ 2 ^ n) :
    Xsum V nb [] ≤ 2 ^ n * ((Fintype.card E).choose (nb + 1) : ℤ) := by
  have h : ∀ ξ ∈ (univ : Finset X), ((#(V ξ)).choose (nb + 1) : ℤ) * allEven V [] ξ ≤ ((Fintype.card E).choose (nb + 1) : ℤ) := by
    intro ξ _
    simp only [allEven, List.map_nil, List.prod_nil, mul_one]
    exact_mod_cast Nat.choose_le_choose _ (card_le_univ _)
  calc Xsum V nb [] ≤ #(univ : Finset X) • ((Fintype.card E).choose (nb + 1) : ℤ) := sum_le_card_nsmul _ _ _ h
    _ = (Fintype.card X : ℤ) * ((Fintype.card E).choose (nb + 1) : ℤ) := by rw [card_univ, nsmul_eq_mul]
    _ ≤ 2 ^ n * ((Fintype.card E).choose (nb + 1) : ℤ) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast hX
end VariableBound.StepChoice
