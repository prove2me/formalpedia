-- Prove2me | solution 1 for VariableBound.Net.StepCost.two_g_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:49:37.781802+00:00
-- url     : https://prove2.me/submissions/d9643bdd-2042-4c2f-81ab-b8c862b46d46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_TopNet
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_StepCost

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.StepCost
open Groundwork ClauseBound.Alg
namespace VariableBound.Net.StepCost
theorem _root_.solution {K : ℕ} (hK : 1 ≤ K) : 2 * (3 * K ^ 8) / K = 6 * K ^ 7 :=
  Nat.div_eq_of_eq_mul_left hK (by ring)
end VariableBound.Net.StepCost
