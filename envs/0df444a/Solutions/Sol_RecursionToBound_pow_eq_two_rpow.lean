-- Prove2me | solution 1 for RecursionToBound.pow_eq_two_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:17:35.579002+00:00
-- url     : https://prove2.me/submissions/1e75f677-6f1b-4347-a591-6f9db29f987e

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

set_option autoImplicit false
section
section
open RecursionToBound
open Finset ClauseBound.ParityChecks UniformInK VariableBound.Net SparsificationLemma MainTheoremForms PairsToBound VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution {x : ℝ} (hx : 0 < x) (j : ℕ) : x ^ j = (2 : ℝ) ^ ((j : ℝ) * lg x) := by
  rw [mul_comm, Real.rpow_mul two_pos.le, lg, Real.rpow_logb two_pos (by norm_num) hx, Real.rpow_natCast]
end RecursionToBound
