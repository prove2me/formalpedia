-- Prove2me | solution 1 for Occ.twoPowFree_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:23:54.84293+00:00
-- url     : https://prove2.me/submissions/58fbeb55-8f08-4a9d-abc1-c3327f8a8765

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Occ_Defs
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_CountKSat_InOut
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Int
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi
import Definitions.Def_Occ_Main
import Theorems.Thm_Occ_free_unary
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_two_pow
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Occ
open Groundwork Groundwork.Prog CountKSat
namespace Occ
theorem _root_.solution : PolyT fun q : (List Unit × Fml) × ℤ => 2 ^ (q.1.1.length - numOcc q.1.2) :=
  PolyT.two_pow free_unary
end Occ
