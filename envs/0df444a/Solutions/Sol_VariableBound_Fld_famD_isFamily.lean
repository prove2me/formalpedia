-- Prove2me | solution 1 for VariableBound.Fld.famD_isFamily
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:56:08.815297+00:00
-- url     : https://prove2.me/submissions/3d9da037-573c-41c1-b1d7-cfd32c6a1a3f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Family
import Definitions.Def_VariableBound_Field_Cert
import Definitions.Def_VariableBound_Family_Main
import Definitions.Def_VariableBound_Field_Main
import Theorems.Thm_VariableBound_Fld_stFamD
import Theorems.Thm_VariableBound_lemFamily


set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
namespace VariableBound.Fld
theorem _root_.solution : StFamD := stFamD VariableBound.lemFamily
end VariableBound.Fld
