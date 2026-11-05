-- Prove2me | solution 1 for Occ.stCountOcc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:40:58.714267+00:00
-- url     : https://prove2.me/submissions/7c0472c7-3205-42ba-822d-7af0219f87a4

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
import Theorems.Thm_Occ_stSameAsFin
import Theorems.Thm_CountKSat_stCntToN
import Theorems.Thm_GraphProblems_exists_toN
import Theorems.Thm_VariableBound_Rename_numSat_eq


set_option autoImplicit false
section
section
open Occ
open Groundwork Groundwork.Prog CountKSat
namespace Occ
theorem _root_.solution : StCountOcc := fun n Φ h => by
  obtain ⟨φ, rfl⟩ := GraphProblems.exists_toN h
  rw [stCntToN, VariableBound.Rename.numSat_eq φ, (stSameAsFin n φ).1, (stSameAsFin n φ).2, mul_comm]
end Occ
