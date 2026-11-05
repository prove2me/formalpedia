-- Prove2me | solution 1 for PaddedDescent.F.cap_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:47:50.823476+00:00
-- url     : https://prove2.me/submissions/02b4abfc-0684-4e6c-9d59-c4cb31c2e8af

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_PaddedDescent_F_Fuel
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
open Groundwork
namespace PaddedDescent.F
theorem _root_.solution {γ : Type} [Enc γ] {pad : U} {d x : γ} (h : len x ≤ pad.length) : cap pad d x = x := if_pos h
end PaddedDescent.F
