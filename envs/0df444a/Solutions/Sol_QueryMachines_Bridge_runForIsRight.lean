-- Prove2me | solution 1 for QueryMachines.Bridge.runForIsRight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:17:27.228812+00:00
-- url     : https://prove2.me/submissions/fe7bbeaf-c4b6-4626-8585-ad238dd48ddb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_CountedToPadded_Compare
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_CountedToPadded_RunFor
import Theorems.Thm_QueryMachines_Bridge_Proof_reaches_size
import Theorems.Thm_QueryMachines_Bridge_Proof_cutAt_some
import Theorems.Thm_QueryMachines_Bridge_Proof_fold_reaches

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge
open Groundwork Groundwork.PolyT PaddedDescent.F Proof
namespace QueryMachines.Bridge
theorem _root_.solution : RunForIsRight := by
  intro α β N _ _ a T S b fuel room h hT hS
  unfold runFor
  rw [cutAt_some hS (reaches_size h)]
  exact fold_reaches hS h fuel hT
end QueryMachines.Bridge
