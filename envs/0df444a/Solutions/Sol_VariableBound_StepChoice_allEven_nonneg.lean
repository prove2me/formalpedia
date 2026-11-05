-- Prove2me | solution 1 for VariableBound.StepChoice.allEven_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:32:12.550303+00:00
-- url     : https://prove2.me/submissions/1882954c-dda2-48ed-9c60-809ffb9371a0

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
import Theorems.Thm_VariableBound_StepChoice_ev_nonneg

set_option autoImplicit false
section
section
open VariableBound VariableBound.StepChoice
open AppVariables Finset
variable {X E ι : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [Fintype X] [Fintype E]
namespace VariableBound.StepChoice
theorem _root_.solution (V : X → Finset E) (L : List (Finset E)) (ξ : X) : 0 ≤ allEven V L ξ := by
  unfold allEven
  refine List.prod_nonneg fun a ha => ?_
  obtain ⟨Λ, -, rfl⟩ := List.mem_map.1 ha
  exact ev_nonneg _
end VariableBound.StepChoice
