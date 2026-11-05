-- Prove2me | solution 1 for RecursionToBound.lin_lg_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:17:44.452827+00:00
-- url     : https://prove2.me/submissions/7a61c312-8cc0-4804-a041-c3ef7cd1a4ef

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
import Theorems.Thm_PairsToBound_lg_cube_le


set_option autoImplicit false
section
section
open RecursionToBound
open Finset ClauseBound.ParityChecks UniformInK VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) (hL : 900 ≤ lg n) : 29 * (lg n + 2) + 19 ≤ (n : ℝ) := by
  have h1 := lg_cube_le hn
  have h2 : (30 * lg n) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith [sq_nonneg (lg n)]
  have h3 : 30 * lg n ≤ n := (sq_le_sq₀ (by linarith) (Nat.cast_nonneg n)).1 h2
  linarith
end RecursionToBound
