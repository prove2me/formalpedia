-- Prove2me | solution 1 for VariableBound.stNeedD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:59:08.111706+00:00
-- url     : https://prove2.me/submissions/4104a433-0ec9-4c10-876a-7b8ac678f57d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Top_ArithNeed
import Theorems.Thm_VariableBound_ArithNeed_needD_le
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open VariableBound
namespace VariableBound
theorem _root_.solution (hU : StUbD) (hA : StArgD) (hL : StLowerD) (hB : UniformInK.StBetaU) : StNeedD :=
  fun _ _ S i _ _ _ _ _ _ hk hK hn17 hlt hD he0 he1 hs hM hrate => ArithNeed.needD_le hU hA hL hB S i hk hK hn17 hlt hD he0 he1 hs hM hrate
end VariableBound
