-- Prove2me | solution 1 for PaddedDescent.length_pad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:54:29.983355+00:00
-- url     : https://prove2.me/submissions/e3d7b3c1-080e-4a2a-a4c5-ad13d46a330a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_PaddedDescent_Host
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_PaddedDescent_Pad
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open PaddedDescent
open Groundwork Sat3 Turing
variable {e : List Bool → ℕ} {A : List Bool × List Unit → Bool}
namespace PaddedDescent
theorem _root_.solution (k : ℕ) : (pad k).length = 2 ^ k := List.length_replicate
end PaddedDescent
