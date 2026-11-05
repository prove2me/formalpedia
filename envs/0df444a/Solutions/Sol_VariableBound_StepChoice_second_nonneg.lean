-- Prove2me | solution 1 for VariableBound.StepChoice.second_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:32:19.851896+00:00
-- url     : https://prove2.me/submissions/3f2c42de-ca92-4a6c-8182-c52e020ed1a1

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
import Theorems.Thm_VariableBound_StepChoice_pp_nonneg

set_option autoImplicit false
section
section
open VariableBound VariableBound.StepChoice
open AppVariables Finset
variable {X E ι : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace VariableBound.StepChoice
theorem _root_.solution (nb rb tb : ℕ) (L : List (Finset E)) : 0 ≤ (1 + pp nb) ^ (rb - L.length) * (1 / 2 ^ tb) * ∑ e : E, (2 : ℚ) ^ load L e := by
  have := pp_nonneg nb
  positivity
end VariableBound.StepChoice
