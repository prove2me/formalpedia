-- Prove2me | solution 1 for PairsToBound.le_of_wide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:14:46.747027+00:00
-- url     : https://prove2.me/submissions/c71ea9d5-46e2-4e6f-b865-760e7f1f7442

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
import Theorems.Thm_PairsToBound_mul_lglg_le_expN
import Theorems.Thm_PairsToBound_expN_le_nine
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_Paper_lg_add_four


set_option autoImplicit false
section
section
open PairsToBound
open MainTheoremForms VariableBound.Paper
namespace PairsToBound
theorem _root_.solution {k k' n : ℕ} (hn : 4 ≤ n) (h : lg n < (k' : ℝ) ^ 4) (hk : k' ^ 2 ≤ 9 * k ^ 2) : (n : ℝ) ≤ 9 * expN k n :=
  (le_mul_of_one_le_right (Nat.cast_nonneg n) (lg_add_four hn).2.2.1).trans ((mul_lglg_le_expN hn h).trans (expN_le_nine hn hk))
end PairsToBound
