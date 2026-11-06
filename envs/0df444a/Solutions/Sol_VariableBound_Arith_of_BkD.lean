-- Prove2me | solution 1 for VariableBound.Arith.of_BkD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:42:08.991869+00:00
-- url     : https://prove2.me/submissions/f4b13bb2-d72e-4cf1-82a3-2c7eb9d94365

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
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open VariableBound VariableBound.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks UniformInK UniformInK.Arith
namespace VariableBound.Arith
theorem _root_.solution {C C₀ k ℓ : ℕ} (h : BkD C C₀ * k ^ 2 ≤ ℓ) : 2 * (102 * C₀ * (aU C C₀ * k)) ^ 2 ≤ ℓ := by
  unfold BkD at h
  rwa [show 2 * (102 * C₀ * (aU C C₀ * k)) ^ 2 = 2 * (102 * C₀ * aU C C₀) ^ 2 * k ^ 2 by ring]
end VariableBound.Arith
