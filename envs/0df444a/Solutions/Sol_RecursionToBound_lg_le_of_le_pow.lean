-- Prove2me | solution 1 for RecursionToBound.lg_le_of_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:17:43.434667+00:00
-- url     : https://prove2.me/submissions/01c3ce2e-eced-49a5-a25c-d385b3cc3956

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_Setting
import Definitions.Def_VariableBound_Params_Ineq
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Definitions.Def_RecursionToBound_Numbers
import Theorems.Thm_VariableBound_Paper_lg_mono


set_option autoImplicit false
section
section
open RecursionToBound
open Finset ClauseBound.ParityChecks UniformInK VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution {Δ j : ℕ} {a : ℝ} (hΔ : 1 ≤ Δ) (ha : 1 ≤ a) (h : (Δ : ℝ) ≤ 2 * a ^ j + 2) : lg Δ ≤ j * lg a + 2 := by
  have hp : 1 ≤ a ^ j := one_le_pow₀ ha
  have h1 : (Δ : ℝ) ≤ 4 * a ^ j := by linarith
  have h2 : lg Δ ≤ lg (4 * a ^ j) := lg_mono (by exact_mod_cast hΔ) h1
  have h3 : lg (4 * a ^ j) = 2 + j * lg a := by
    unfold lg
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow, Real.logb_self_eq_one one_lt_two]
    norm_num
  linarith
end RecursionToBound
