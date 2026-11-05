-- Prove2me | solution 1 for PaddedDescent.padM_runs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:35:39.233016+00:00
-- url     : https://prove2.me/submissions/06358ad9-12e9-4c85-a61d-e139e047df2d

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
import Theorems.Thm_PaddedDescent_padM_reaches
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
open PaddedDescent
open Groundwork Sat3 Turing
variable {e : List Bool → ℕ} {A : List Bool × List Unit → Bool}
namespace PaddedDescent
theorem _root_.solution (e : List Bool → ℕ) (A : List Bool × List Unit → Bool) (x : List Bool) :
    (padM e A).Runs x (e x + 1) (2 * x.length + 2 * 2 ^ e x + 3) (A (x, pad (e x))) :=
  padM_reaches x (e x) 0 (by omega)
end PaddedDescent
