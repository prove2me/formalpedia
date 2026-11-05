-- Prove2me | solution 1 for PaddedDescent.F.stEncInj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:13:38.751195+00:00
-- url     : https://prove2.me/submissions/675a595a-4eb4-404b-972b-e8421f18449f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_PaddedDescent_F_MarkCode
import Theorems.Thm_PaddedDescent_F_Mark_Code_enc_append_inj
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F
theorem _root_.solution : StEncInj := fun _ _ _ _ _ _ h0 hb hl h => Mark.Code.enc_append_inj h0 hb hl h
end PaddedDescent.F
