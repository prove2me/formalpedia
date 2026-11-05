-- Prove2me | solution 1 for Wrap.lastStepsArePolynomialTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:52:35.782341+00:00
-- url     : https://prove2.me/submissions/13b8763a-4c4a-4214-8395-63272ef0fed0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Defs
import Definitions.Def_Wrap_CodingExists
import Definitions.Def_Wrap_Sim
import Definitions.Def_Wrap_FrontEnd
import Definitions.Def_Wrap_Arith
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_WidthThree_Rates
import Definitions.Def_VariableBound_Paper_MainTheorem
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Rename_End
import Definitions.Def_Wrap_Main
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_VariableBound_Rename_anyBit_polyT
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork
open scoped NNReal
namespace Wrap
theorem _root_.solution : LastStepsArePolynomialTime := ⟨PolyT.id', VariableBound.Rename.anyBit_polyT⟩
end Wrap
