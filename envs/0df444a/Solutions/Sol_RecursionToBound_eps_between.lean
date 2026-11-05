-- Prove2me | solution 1 for RecursionToBound.eps_between
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:26:03.649887+00:00
-- url     : https://prove2.me/submissions/7e27b92e-3ff3-496b-b406-f523d9f7d5fb

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
import Theorems.Thm_RecursionToBound_epsOf_cast
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open RecursionToBound
open Finset ClauseBound.ParityChecks UniformInK VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution {r : ℕ × ℕ} {e : ℝ} (he1 : e ≤ 1) (h1 : e ≤ (r.1 : ℝ) / r.2) (h2 : (r.1 : ℝ) / r.2 ≤ 2 * e) :
    e ≤ ((epsOf r : ℚ) : ℝ) ∧ ((epsOf r : ℚ) : ℝ) ≤ 2 * e ∧ ((epsOf r : ℚ) : ℝ) ≤ 1 := by
  rw [epsOf_cast]
  exact ⟨le_min h1 he1, (min_le_left _ _).trans h2, min_le_right _ _⟩
end RecursionToBound
