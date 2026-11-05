-- Prove2me | solution 1 for ThmVariables.e_ge_n
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:31:06.704641+00:00
-- url     : https://prove2.me/submissions/07b6caee-0caf-4eeb-be65-7f1aca08a0f4

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
import Theorems.Thm_ThmVariables_K_le_n
import Theorems.Thm_VariableBound_Paper_lg_mono
import Theorems.Thm_VariableBound_Paper_one_le_lg
import Theorems.Thm_VariableBound_VariablesA_K_le_n


set_option autoImplicit false
section
section
open ThmVariables
open Turing CliqueLevels MainTheoremForms VariableBound.Paper
open Sat3 (CNF)
variable {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}
namespace ThmVariables
theorem _root_.solution (hL : Levels K e C₀) {n l : ℕ} (h : ThmVariables.IsLevel K n l) : 1 / lg n ^ C₀ ≤ e l := by
  have h1 := one_le_lg (hL.K_two l)
  have h2 : lg (K l) ≤ lg n := lg_mono (by exact_mod_cast (by have := hL.K_two l; omega : 0 < K l)) (by exact_mod_cast K_le_n h)
  refine le_trans ?_ (hL.e_ge l)
  exact one_div_le_one_div_of_le (pow_pos (by linarith : 0 < lg (K l)) _) (pow_le_pow_left₀ (by linarith) h2 _)
end ThmVariables
