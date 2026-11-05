-- Prove2me | solution 1 for VariableBound.StepChoice.lt_rb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:26:26.606632+00:00
-- url     : https://prove2.me/submissions/3029188f-2971-4b4a-8773-0b74d5353b39

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
theorem _root_.solution (V : X → Finset E) (nb β rb : ℕ) (L : List (Finset E)) (hrb : 3 ^ rb * 2 ^ β < 4 ^ rb) (hl : L.length ≤ rb) (hpos : 0 < Xsum V nb L)
    (h : 4 ^ L.length * Xsum V nb L ≤ 3 ^ L.length * 2 ^ β) : L.length < rb := by
  rcases hl.lt_or_eq with h' | h'
  · exact h'
  · exfalso
    rw [h'] at h
    have h1 : (3 : ℤ) ^ rb * 2 ^ β < 4 ^ rb := by exact_mod_cast hrb
    have h2 : (4 : ℤ) ^ rb * 1 ≤ 4 ^ rb * Xsum V nb L := mul_le_mul_of_nonneg_left (by omega) (by positivity)
    linarith
end VariableBound.StepChoice
