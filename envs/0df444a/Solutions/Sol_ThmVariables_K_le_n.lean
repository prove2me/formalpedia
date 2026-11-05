-- Prove2me | solution 1 for ThmVariables.K_le_n
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:36:30.661363+00:00
-- url     : https://prove2.me/submissions/5ee6e64e-cda8-4947-80d7-bd30cd44306c

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
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ThmVariables
open Turing CliqueLevels MainTheoremForms VariableBound.Paper
open Sat3 (CNF)
variable {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}
namespace ThmVariables
theorem _root_.solution {n l : ℕ} (h : ThmVariables.IsLevel K n l) : K l ≤ n := (Nat.le_self_pow (by norm_num) _).trans h.1
end ThmVariables
