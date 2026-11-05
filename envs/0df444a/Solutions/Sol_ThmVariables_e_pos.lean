-- Prove2me | solution 1 for ThmVariables.e_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:37:26.957191+00:00
-- url     : https://prove2.me/submissions/11922704-1844-4d08-af2c-02758049d254

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmVariables_Defs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_ThmVariables_Bound
import Theorems.Thm_VariableBound_Paper_one_le_lg


set_option autoImplicit false
section
section
open ThmVariables
open Turing CliqueLevels MainTheoremForms VariableBound.Paper
open Sat3 (CNF)
variable {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}
namespace ThmVariables
theorem _root_.solution (hL : Levels K e C₀) (l : ℕ) : 0 < e l := by
  have h : 0 < Real.logb 2 (K l) := lt_of_lt_of_le one_pos (one_le_lg (hL.K_two l))
  exact lt_of_lt_of_le (by positivity) (hL.e_ge l)
end ThmVariables
