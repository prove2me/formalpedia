-- Prove2me | solution 1 for PairsToBound.mul_lg_le_expN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:36:53.767666+00:00
-- url     : https://prove2.me/submissions/0251111b-a891-4703-a5b2-7b594e2f34fd

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
import Theorems.Thm_PairsToBound_lg_le_div_sqrt
import Theorems.Thm_PairsToBound_div_sqrt_le_base
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_Paper_expN_eq
import Theorems.Thm_VariableBound_Paper_one_le_lg


set_option autoImplicit false
section
section
open PairsToBound
open MainTheoremForms VariableBound.Paper
namespace PairsToBound
theorem _root_.solution {k n : ℕ} (hk : 1 ≤ k) (hn : 4 ≤ n) : (k : ℝ) * lg n ≤ expN k n := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 := (lg_le_div_sqrt (n := n) (by omega)).trans (div_sqrt_le_base hn)
  have h0 : 0 ≤ lg n := by linarith [one_le_lg (m := n) (by omega)]
  rw [expN_eq]
  exact mul_le_mul (by nlinarith) h1 h0 (by positivity)
end PairsToBound
