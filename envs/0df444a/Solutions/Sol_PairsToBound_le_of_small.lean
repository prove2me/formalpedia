-- Prove2me | solution 1 for PairsToBound.le_of_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:47.812896+00:00
-- url     : https://prove2.me/submissions/12ecbfcf-b317-4db8-b325-3bcaaa7e0953

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
import Theorems.Thm_PairsToBound_div_sqrt_level_le_base
import Theorems.Thm_VariableBound_Paper_expN_eq
import Theorems.Thm_VariableBound_Paper_one_le_lg
import Theorems.Thm_VariableBound_Paper_two_le_base


set_option autoImplicit false
section
section
open PairsToBound
open MainTheoremForms VariableBound.Paper
namespace PairsToBound
theorem _root_.solution {K₀ k n : ℕ} {D : ℝ} (hK : 2 ≤ K₀) (hk : 1 ≤ k) (hn : 4 ≤ n) (h : n < K₀ ^ 17) (hD : Real.sqrt (17 * lg K₀) ≤ D) : (n : ℝ) ≤ D * expN k n := by
  have hs : 0 < Real.sqrt (17 * lg K₀) := Real.sqrt_pos.2 (by linarith [one_le_lg hK])
  have h1 := div_sqrt_level_le_base hn h
  rw [div_le_iff₀ hs] at h1
  have hb := two_le_base hn
  have h2 : (n : ℝ) * lg (lg n) / Real.sqrt (lg n) ≤ expN k n := by
    rw [expN_eq]
    exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by exact_mod_cast hk))
  calc (n : ℝ) ≤ (n : ℝ) * lg (lg n) / Real.sqrt (lg n) * Real.sqrt (17 * lg K₀) := h1
    _ ≤ expN k n * D := mul_le_mul h2 hD hs.le (by linarith)
    _ = D * expN k n := mul_comm _ _
end PairsToBound
