-- Prove2me | solution 1 for VariableBound.Fld.decW_mulW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:14:41.612661+00:00
-- url     : https://prove2.me/submissions/c6bf560b-8ba4-467e-808a-2b8ec20e98b3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Ring
import Definitions.Def_VariableBound_Field_Quot
import Definitions.Def_VariableBound_Field_Transfer
import Definitions.Def_VariableBound_Field_Search
import Theorems.Thm_VariableBound_Fld_decR_mulW
import Theorems.Thm_VariableBound_Fld_root_pow
import Theorems.Thm_VariableBound_Fld_two_eq_zero_FW


set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Polynomial
namespace VariableBound.Fld
theorem _root_.solution (g : List Bool) {x : List Bool} (hx : x.length = g.length) (y : List Bool) : decW g (mulW g x y) = decW g x * decW g y :=
  decR_mulW (two_eq_zero_FW g) (root_pow g) hx y
end VariableBound.Fld
