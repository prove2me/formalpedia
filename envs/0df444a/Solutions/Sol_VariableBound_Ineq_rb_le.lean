-- Prove2me | solution 1 for VariableBound.Ineq.rb_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:55:12.394947+00:00
-- url     : https://prove2.me/submissions/1882732e-1df8-453e-ac6d-78df5d7c3931

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Ineq

set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Ineq
namespace VariableBound.Ineq
theorem _root_.solution {β rb : ℕ} (h : IsRb β rb) : (rb : ℝ) ≤ 2.41 * β + 1 := by
  rcases Nat.eq_zero_or_pos rb with rfl | hpos
  · have : (0 : ℝ) ≤ β := Nat.cast_nonneg β
    push_cast
    linarith
  · obtain ⟨j, rfl⟩ : ∃ j, rb = j + 1 := ⟨rb - 1, by omega⟩
    have h1 : 4 ^ j ≤ 3 ^ j * 2 ^ β := not_lt.1 (h.2 j (Nat.lt_succ_self j))
    have h2 : (2 : ℕ) ^ 100 * 3 ^ 241 ≤ 4 ^ 241 := by norm_num
    have h3 : 2 ^ (100 * j) * 3 ^ (241 * j) ≤ 2 ^ (241 * β) * 3 ^ (241 * j) := by
      calc 2 ^ (100 * j) * 3 ^ (241 * j) = (2 ^ 100 * 3 ^ 241) ^ j := by rw [mul_pow, ← pow_mul, ← pow_mul]
        _ ≤ (4 ^ 241) ^ j := Nat.pow_le_pow_left h2 j
        _ = (4 ^ j) ^ 241 := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ (3 ^ j * 2 ^ β) ^ 241 := Nat.pow_le_pow_left h1 241
        _ = 2 ^ (241 * β) * 3 ^ (241 * j) := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm, mul_comm β, mul_comm j]
    have h4 : 100 * j ≤ 241 * β := (Nat.pow_le_pow_iff_right (by norm_num)).1 (Nat.le_of_mul_le_mul_right h3 (by positivity))
    have h5 : (100 : ℝ) * j ≤ 241 * β := by exact_mod_cast h4
    push_cast
    linarith
end VariableBound.Ineq
