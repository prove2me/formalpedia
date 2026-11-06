-- Prove2me | solution 1 for Occ.stNumOccLe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:02:56.996209+00:00
-- url     : https://prove2.me/submissions/e0bf7778-063f-4527-95c8-2021e0cf8f3c

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

set_option autoImplicit false
section
section
open Occ
open Groundwork Groundwork.Prog CountKSat
namespace Occ
theorem _root_.solution : StNumOccLe := fun n Φ h => by
  have h1 : Eight.occurring Φ ⊆ Finset.range n := fun v hv => Finset.mem_range.2 (lt_of_mem_occurring h hv)
  have h2 := Finset.card_le_card h1
  rwa [Finset.card_range] at h2
end Occ
