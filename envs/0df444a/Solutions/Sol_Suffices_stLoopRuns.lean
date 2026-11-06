-- Prove2me | solution 1 for Suffices.stLoopRuns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:03:30.695087+00:00
-- url     : https://prove2.me/submissions/685ef2b0-3edb-4c2f-b621-f461ca70501f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Sizes
import Definitions.Def_Exits_Runs
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_Suffices_Loop
import Theorems.Thm_Suffices_stLoopRunsOf
import Theorems.Thm_Exits_stWalkUntil


set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Paper SparsificationLemma Enumerate Exits
open Groundwork.Sparsify (leaves)
namespace Suffices
theorem _root_.solution : StLoopRuns := stLoopRunsOf stWalkUntil
end Suffices
