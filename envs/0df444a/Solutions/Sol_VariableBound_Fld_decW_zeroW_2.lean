-- Prove2me | solution 2 for VariableBound.Fld.decW_zeroW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:29:44.496141+00:00
-- url     : https://prove2.me/submissions/6c487f57-6fff-4735-9e98-b8363a54c63d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Ring
import Definitions.Def_VariableBound_Field_Quot
import Definitions.Def_VariableBound_Field_Transfer
import Definitions.Def_VariableBound_Field_Search
import Theorems.Thm_VariableBound_Fld_decR_zeroW


set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Polynomial
namespace VariableBound.Fld
theorem _root_.solution (g : List Bool) : decW g (zeroW g) = 0 := decR_zeroW _ _
end VariableBound.Fld
