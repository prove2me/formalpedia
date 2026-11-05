-- Prove2me | solution 1 for VariableBound.StepChoice.load_of_ups
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:50:56.001685+00:00
-- url     : https://prove2.me/submissions/98000e79-e4ec-4308-b3e0-da44f1fb63c3

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
import Theorems.Thm_VariableBound_StepChoice_first_nonneg

set_option autoImplicit false
section
section
open VariableBound VariableBound.StepChoice
open AppVariables Finset
variable {X E ι : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace VariableBound.StepChoice
theorem _root_.solution (V : X → Finset E) (nb β rb tb : ℕ) (L : List (Finset E)) (h : Ups V nb β rb tb L ≤ 2) (e : E) : load L e ≤ tb + 1 := by
  have h1 : (1 + pp nb) ^ (rb - L.length) * (1 / 2 ^ tb) * ∑ e : E, (2 : ℚ) ^ load L e ≤ 2 := by
    have := first_nonneg V nb β L
    unfold Ups at h
    linarith
  have h2 : (2 : ℚ) ^ load L e ≤ ∑ e : E, (2 : ℚ) ^ load L e := single_le_sum (f := fun e => (2 : ℚ) ^ load L e) (fun _ _ => by positivity) (mem_univ e)
  have h3 : (1 : ℚ) ≤ (1 + pp nb) ^ (rb - L.length) := one_le_pow₀ (by have := pp_nonneg nb; linarith)
  have h4 : 1 * (1 / 2 ^ tb) * (2 : ℚ) ^ load L e ≤ 2 := le_trans (by gcongr) h1
  have h5 : (2 : ℚ) ^ load L e ≤ 2 ^ (tb + 1) := by
    rw [one_mul, one_div, inv_mul_le_iff₀ (by positivity)] at h4
    rw [pow_succ]; linarith
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).1 h5
end VariableBound.StepChoice
