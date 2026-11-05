-- Prove2me | solution 1 for VariableBound.Fld.decW_xorW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:26:55.738371+00:00
-- url     : https://prove2.me/submissions/43022d5f-342a-4918-813d-3ed0cd01dec9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Ring
import Definitions.Def_VariableBound_Field_Quot
import Definitions.Def_VariableBound_Field_Transfer
import Definitions.Def_VariableBound_Field_Search
import Theorems.Thm_VariableBound_Fld_decR_xorW
import Theorems.Thm_VariableBound_Fld_two_eq_zero_FW


set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Polynomial
namespace VariableBound.Fld
theorem _root_.solution (g : List Bool) {x y : List Bool} (h : x.length = y.length) : decW g (xorW x y) = decW g x + decW g y :=
  decR_xorW (two_eq_zero_FW g) _ x y h
end VariableBound.Fld
