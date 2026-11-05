-- Prove2me | solution 1 for VariableBound.StepChoice.load_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:26:23.760021+00:00
-- url     : https://prove2.me/submissions/1567671b-7534-4fa4-86a5-3b5e869ac2bb

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
omit [Fintype E]
namespace VariableBound.StepChoice
theorem _root_.solution (L : List (Finset E)) (Γ : Finset E) (e : E) : load (L ++ [Γ]) e = load L e + if e ∈ Γ then 1 else 0 := by
  unfold load
  rw [List.filter_append, List.length_append]
  by_cases h : e ∈ Γ <;> simp [h]
end VariableBound.StepChoice
