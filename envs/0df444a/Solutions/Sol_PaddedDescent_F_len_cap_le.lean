-- Prove2me | solution 1 for PaddedDescent.F.len_cap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:33:36.522192+00:00
-- url     : https://prove2.me/submissions/999e75f1-84ce-442a-80d6-5c5a62a10d6b

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
theorem _root_.solution {γ : Type} [Enc γ] (pad : U) (d x : γ) : len (cap pad d x) ≤ pad.length + len d := by
  unfold cap; split_ifs <;> omega
end PaddedDescent.F
