-- Prove2me | solution 1 for VariableBound.Paper.two_le_expM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:17:10.249514+00:00
-- url     : https://prove2.me/submissions/2d2799c5-013c-41d4-bda2-94e0b2df5752

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
import Theorems.Thm_VariableBound_Paper_one_le_lg
import Theorems.Thm_VariableBound_Paper_two_sqrt_lg_le

set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms
namespace VariableBound.Paper
theorem _root_.solution {k m : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) : 2 ≤ expM k m := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : 0 < Real.sqrt (lg m) := Real.sqrt_pos.2 (by linarith [one_le_lg hm])
  have h2 := two_sqrt_lg_le (m := m) (by omega)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold expM
  rw [le_div_iff₀ hs]
  nlinarith
end VariableBound.Paper
