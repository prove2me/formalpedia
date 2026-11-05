-- Prove2me | solution 1 for VariableBound.ArithNat.UbD_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:35:53.85081+00:00
-- url     : https://prove2.me/submissions/c7c49370-d254-474b-9227-f3ff7b27dad5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_UniformInK_Top_ArithNat
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Budget
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Top_ArithNat
import Theorems.Thm_ClauseBound_ParityChecks_LD_two_pow
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_UniformInK_ArithNat_two_le_D
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open VariableBound VariableBound.ArithNat
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks UniformInK UniformInK.ArithNat VariableBound.Net
variable {β k K n C₀ : ℕ}
namespace VariableBound.ArithNat
theorem _root_.solution (hB : StBounds) (hβ : 1 ≤ β) (hn : 1 ≤ n) : UbD k K n (2 ^ β) ≤ 140 * k * n * (β + 1) + 18 * K ^ 16 := by
  have h := (hB k K n (2 ^ β) hn (two_le_D hβ)).1
  rw [LD_two_pow] at h
  calc UbD k K n (2 ^ β) ≤ 140 * k * n * (β + 1) + 2 * (3 * K ^ 8) ^ 2 := h
    _ = 140 * k * n * (β + 1) + 18 * K ^ 16 := by ring
end VariableBound.ArithNat
