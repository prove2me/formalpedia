-- Prove2me | solution 1 for VariableBound.Paper.shiftN_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:51:55.632286+00:00
-- url     : https://prove2.me/submissions/1a80bc8e-d91a-4750-b395-442a03545c0b

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
import Theorems.Thm_VariableBound_Paper_lg_add_four

set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms
namespace VariableBound.Paper
theorem _root_.solution (k : ℕ) {n : ℕ} (hn : 4 ≤ n) : (k : ℝ) ^ 2 * n * SatK.rN 1 (1 / 2) n ≤ 2 * expN k n := by
  obtain ⟨hL2, hLL', hl1, hl0, hl'⟩ := lg_add_four hn
  have hs : 0 < Real.sqrt (lg n) := Real.sqrt_pos.2 (by linarith)
  have hle : Real.sqrt (lg n) ≤ Real.sqrt (lg ((n : ℝ) + 4)) := Real.sqrt_le_sqrt hLL'
  have hr : SatK.rN 1 (1 / 2) n ≤ 2 * (lg (lg n) / Real.sqrt (lg n)) := by
    unfold SatK.rN
    rw [← Real.sqrt_eq_rpow, pow_one]
    change lg (lg ((n : ℝ) + 4)) / Real.sqrt (lg ((n : ℝ) + 4)) ≤ _
    calc lg (lg ((n : ℝ) + 4)) / Real.sqrt (lg ((n : ℝ) + 4)) ≤ lg (lg ((n : ℝ) + 4)) / Real.sqrt (lg n) :=
          div_le_div_of_nonneg_left hl0 hs hle
      _ ≤ 2 * lg (lg n) / Real.sqrt (lg n) := div_le_div_of_nonneg_right hl' hs.le
      _ = 2 * (lg (lg n) / Real.sqrt (lg n)) := mul_div_assoc _ _ _
  calc (k : ℝ) ^ 2 * n * SatK.rN 1 (1 / 2) n ≤ (k : ℝ) ^ 2 * n * (2 * (lg (lg n) / Real.sqrt (lg n))) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
    _ = 2 * expN k n := by unfold expN; ring
end VariableBound.Paper
