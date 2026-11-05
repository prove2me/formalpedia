-- Prove2me | solution 1 for VariableBound.StepChoice.x_of_ups
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:34:05.493517+00:00
-- url     : https://prove2.me/submissions/67ddf795-d2a8-4e90-9377-5727e1e9d246

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
import Theorems.Thm_VariableBound_StepChoice_second_nonneg

set_option autoImplicit false
section
section
open VariableBound VariableBound.StepChoice
open AppVariables Finset
variable {X E ι : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace VariableBound.StepChoice
theorem _root_.solution (V : X → Finset E) (nb β rb tb : ℕ) (L : List (Finset E)) (hβ : 1 ≤ β) (h : Ups V nb β rb tb L ≤ 2) :
    4 ^ L.length * Xsum V nb L ≤ 3 ^ L.length * 2 ^ β := by
  have h1 : (4 / 3 : ℚ) ^ L.length * (Xsum V nb L : ℚ) / 2 ^ (β - 1) ≤ 2 := by
    have := second_nonneg nb rb tb L
    unfold Ups at h
    linarith
  have h2 : (2 : ℚ) ^ β = 2 * 2 ^ (β - 1) := by
    obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]; ring
  have h3 : (4 : ℚ) ^ L.length * (Xsum V nb L : ℚ) ≤ 3 ^ L.length * 2 ^ β := by
    rw [div_le_iff₀ (by positivity), div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h1
    rw [h2]; linarith
  exact_mod_cast h3
end VariableBound.StepChoice
