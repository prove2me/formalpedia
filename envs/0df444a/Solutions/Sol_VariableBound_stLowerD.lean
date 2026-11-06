-- Prove2me | solution 1 for VariableBound.stLowerD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:54:42.508109+00:00
-- url     : https://prove2.me/submissions/1611e0e8-7f4f-4d7a-9df5-68f732a6b21d

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
import Theorems.Thm_VariableBound_ArithNat_lowerD
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open VariableBound
namespace VariableBound
theorem _root_.solution (hB : Net.StBounds) : StLowerD := fun _ _ _ _ _ hβ hkβ hK hn17 hlt => ArithNat.lowerD hB hβ hkβ hK hn17 hlt
end VariableBound
