-- Prove2me | solution 1 for PairsToBound.mul_lglg_le_expN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:29:36.930761+00:00
-- url     : https://prove2.me/submissions/a70ff2d0-c40d-4672-93e6-5be86fac49a3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_PairsToBound_Arith
import Theorems.Thm_VariableBound_Paper_lg_add_four


set_option autoImplicit false
section
section
open PairsToBound
open MainTheoremForms VariableBound.Paper
namespace PairsToBound
theorem _root_.solution {k n : ℕ} (hn : 4 ≤ n) (h : lg n < (k : ℝ) ^ 4) : (n : ℝ) * lg (lg n) ≤ expN k n := by
  obtain ⟨hL2, -, hl1, -, -⟩ := lg_add_four hn
  have hs : 0 < Real.sqrt (lg n) := Real.sqrt_pos.2 (by linarith)
  have hsk : Real.sqrt (lg n) ≤ (k : ℝ) ^ 2 := Real.sqrt_le_iff.2 ⟨by positivity, by rw [← pow_mul]; exact h.le⟩
  unfold expN
  rw [le_div_iff₀ hs]
  calc (n : ℝ) * lg (lg n) * Real.sqrt (lg n) ≤ (n : ℝ) * lg (lg n) * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hsk (mul_nonneg (Nat.cast_nonneg n) (by linarith))
    _ = (k : ℝ) ^ 2 * n * lg (lg n) := by ring
end PairsToBound
