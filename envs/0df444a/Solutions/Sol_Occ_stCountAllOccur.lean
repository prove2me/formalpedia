-- Prove2me | solution 1 for Occ.stCountAllOccur
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:03:09.73221+00:00
-- url     : https://prove2.me/submissions/d836c55d-803c-4086-aee3-1ce961f65706

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
import Theorems.Thm_Occ_stCountOcc

set_option autoImplicit false
section
section
open Occ
open Groundwork Groundwork.Prog CountKSat
namespace Occ
theorem _root_.solution : StCountAllOccur := fun n Φ h h2 => by
  have h3 : Eight.occurring Φ = Finset.range n := by
    ext v
    rw [Finset.mem_range]
    exact ⟨lt_of_mem_occurring h, fun hv => mem_occurring.2 (h2 v hv)⟩
  rw [stCountOcc n Φ h, numOcc, h3, Finset.card_range, Nat.sub_self, pow_zero, mul_one]
end Occ
