-- Prove2me | solution 1 for VariableBound.Paper.lg_le_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:37:25.622781+00:00
-- url     : https://prove2.me/submissions/e71f678b-5790-4810-8088-3cf051d47f15

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Definitions.Def_VariableBound_Paper_Arith

set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms
namespace VariableBound.Paper
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) : lg m ≤ (m : ℝ) - 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have h : ((j + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast (Nat.lt_two_pow_self (n := j))
  unfold lg
  rw [Real.logb_le_iff_le_rpow one_lt_two (by positivity)]
  have e : ((j + 1 : ℕ) : ℝ) - 1 = (j : ℝ) := by push_cast; ring
  rw [e, Real.rpow_natCast]
  exact h
end VariableBound.Paper
