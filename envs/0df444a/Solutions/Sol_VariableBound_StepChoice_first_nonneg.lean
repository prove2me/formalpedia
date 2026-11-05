-- Prove2me | solution 1 for VariableBound.StepChoice.first_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:39:31.301963+00:00
-- url     : https://prove2.me/submissions/2880d811-21ad-4ca6-9f52-122eb7513238

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
import Theorems.Thm_VariableBound_StepChoice_Xsum_nonneg

set_option autoImplicit false
section
section
open VariableBound VariableBound.StepChoice
open AppVariables Finset
variable {X E ι : Type} [Fintype X] [Fintype E] [DecidableEq E]
omit [Fintype E]
namespace VariableBound.StepChoice
theorem _root_.solution (V : X → Finset E) (nb β : ℕ) (L : List (Finset E)) : (0 : ℚ) ≤ (4 / 3) ^ L.length * (Xsum V nb L : ℚ) / 2 ^ (β - 1) := by
  have : (0 : ℚ) ≤ (Xsum V nb L : ℚ) := by exact_mod_cast Xsum_nonneg V nb L
  positivity
end VariableBound.StepChoice
