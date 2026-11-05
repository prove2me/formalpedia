-- Prove2me | solution 1 for ThmVariables.expVariablesA_le_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:17:48.512085+00:00
-- url     : https://prove2.me/submissions/0e2c14f8-d2ec-4dcf-9456-e49d88306669

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
import Theorems.Thm_VariableBound_Paper_lg_mono


set_option autoImplicit false
section
section
open ThmVariables
open Turing CliqueLevels MainTheoremForms VariableBound.Paper
open Sat3 (CNF)
variable {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}
namespace ThmVariables
theorem _root_.solution {k n : ℕ} {e e' : ℝ} (hk : 1 ≤ k) (he : 0 < e) (h1 : e ≤ e') (h2 : e' ≤ 2 * e) (h3 : e' ≤ 1) : expVariablesA k n e' ≤ 2 * expVariablesA k n e := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have he' : 0 < e' := lt_of_lt_of_le he h1
  have g0 : 0 ≤ lg (k / e') := Real.logb_nonneg one_lt_two (by rw [le_div_iff₀ he']; linarith)
  have g1 : lg (k / e') ≤ lg (k / e) := lg_mono (by positivity) (div_le_div_of_nonneg_left (by linarith) he h1)
  unfold expVariablesA
  calc (k : ℝ) ^ 2 * e' * n * lg (k / e') ≤ (k : ℝ) ^ 2 * (2 * e) * n * lg (k / e) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) (Nat.cast_nonneg n)) g1 g0 (by positivity)
    _ = 2 * ((k : ℝ) ^ 2 * e * n * lg (k / e)) := by ring
end ThmVariables
