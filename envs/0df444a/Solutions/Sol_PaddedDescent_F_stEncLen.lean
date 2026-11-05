-- Prove2me | solution 1 for PaddedDescent.F.stEncLen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:02:48.779198+00:00
-- url     : https://prove2.me/submissions/cdda034b-1c57-467f-9912-d8d2292f1092

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_PaddedDescent_F_MarkCode
import Theorems.Thm_PaddedDescent_F_Mark_Code_length_enc
import Theorems.Thm_Groundwork_Decode_length_enc
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F
theorem _root_.solution : StEncLen := fun _ _ x h0 => Mark.Code.length_enc h0 x
end PaddedDescent.F
