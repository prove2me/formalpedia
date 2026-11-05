-- Prove2me | solution 1 for VariableBound.Fld.decW_oneW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:30:17.1175+00:00
-- url     : https://prove2.me/submissions/4abc6a9e-faba-43d6-8e3c-90b6e7b4208e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Ring
import Definitions.Def_VariableBound_Field_Quot
import Definitions.Def_VariableBound_Field_Transfer
import Definitions.Def_VariableBound_Field_Search
import Theorems.Thm_VariableBound_Fld_decR_oneW


set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Polynomial
namespace VariableBound.Fld
theorem _root_.solution (g : List Bool) : decW g (oneW g) = 1 := decR_oneW _ _
end VariableBound.Fld
