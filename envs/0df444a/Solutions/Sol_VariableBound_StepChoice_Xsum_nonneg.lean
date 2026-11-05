-- Prove2me | solution 1 for VariableBound.StepChoice.Xsum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:32:54.257103+00:00
-- url     : https://prove2.me/submissions/920a28ae-2930-495e-ac2d-07219e0f5493

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
import Theorems.Thm_VariableBound_StepChoice_allEven_nonneg

set_option autoImplicit false
section
section
open VariableBound VariableBound.StepChoice
open AppVariables Finset
variable {X E ι : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [Fintype E]
namespace VariableBound.StepChoice
theorem _root_.solution (V : X → Finset E) (nb : ℕ) (L : List (Finset E)) : 0 ≤ Xsum V nb L :=
  sum_nonneg fun ξ _ => mul_nonneg (by positivity) (allEven_nonneg V L ξ)
end VariableBound.StepChoice
