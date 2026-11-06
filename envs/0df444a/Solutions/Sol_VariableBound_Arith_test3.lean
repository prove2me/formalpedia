-- Prove2me | solution 1 for VariableBound.Arith.test3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:42:10.037204+00:00
-- url     : https://prove2.me/submissions/eb67b8fe-8bd4-4a0c-aa13-23c2311665f1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_UniformInK_Top_ArithTop
import Definitions.Def_UniformInK_Top_ArithTop
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Top_ArithTop
import Theorems.Thm_ClauseBound_ParityChecks_LD_two_pow
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open VariableBound VariableBound.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks UniformInK UniformInK.Arith
namespace VariableBound.Arith
theorem _root_.solution {β n : ℕ} (hb : β + 3 ≤ 2 ^ β) (h6 : (2 ^ β) ^ 6 ≤ n) : 29 * LD (2 ^ β) + 19 ≤ n := by
  rw [LD_two_pow]
  refine le_trans ?_ h6
  generalize 2 ^ β = D at hb
  have h3 : 3 ^ 5 ≤ D ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have h4 : 3 ^ 5 * D ≤ D ^ 6 := by rw [pow_succ D 5]; exact Nat.mul_le_mul_right D h3
  omega
end VariableBound.Arith
