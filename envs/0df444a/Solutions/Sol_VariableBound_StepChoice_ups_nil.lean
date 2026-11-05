-- Prove2me | solution 1 for VariableBound.StepChoice.ups_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:40:16.736952+00:00
-- url     : https://prove2.me/submissions/877a300d-1fd4-4362-833e-236b707c75b3

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
import Theorems.Thm_VariableBound_StepChoice_Xsum_nil_le

set_option autoImplicit false
section
section
open VariableBound VariableBound.StepChoice
open AppVariables Finset
variable {X E ι : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace VariableBound.StepChoice
theorem _root_.solution (V : X → Finset E) (n nb rb tb : ℕ) (hX : Fintype.card X ≤ 2 ^ n) (ht : (Fintype.card E : ℚ) * (1 + pp nb) ^ rb ≤ 2 ^ tb) :
    Ups V nb (beta n (Fintype.card E) nb) rb tb [] ≤ 2 := by
  have h1 : Xsum V nb [] ≤ 2 ^ (beta n (Fintype.card E) nb - 1) := by
    refine (Xsum_nil_le V nb n hX).trans ?_
    have : beta n (Fintype.card E) nb - 1 = n + Nat.clog 2 ((Fintype.card E).choose (nb + 1)) := by unfold beta; omega
    rw [this, pow_add]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact_mod_cast Nat.le_pow_clog (by norm_num) _
  have h1' : (Xsum V nb [] : ℚ) ≤ 2 ^ (beta n (Fintype.card E) nb - 1) := by exact_mod_cast h1
  unfold Ups
  have e1 : (4 / 3 : ℚ) ^ ([] : List (Finset E)).length * (Xsum V nb [] : ℚ) / 2 ^ (beta n (Fintype.card E) nb - 1) ≤ 1 := by
    rw [List.length_nil, pow_zero, one_mul, div_le_one (by positivity)]
    exact h1'
  have e2 : (1 + pp nb) ^ (rb - ([] : List (Finset E)).length) * (1 / 2 ^ tb) * ∑ e : E, (2 : ℚ) ^ load [] e ≤ 1 := by
    have : ∑ e : E, (2 : ℚ) ^ load [] e = Fintype.card E := by simp [load]
    rw [this, List.length_nil, Nat.sub_zero]
    calc (1 + pp nb) ^ rb * (1 / 2 ^ tb) * (Fintype.card E : ℚ) = (Fintype.card E : ℚ) * (1 + pp nb) ^ rb / 2 ^ tb := by ring
      _ ≤ 1 := by rw [div_le_one (by positivity)]; exact ht
  linarith
end VariableBound.StepChoice
