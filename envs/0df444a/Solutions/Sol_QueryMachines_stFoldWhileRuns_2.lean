-- Prove2me | solution 2 for QueryMachines.stFoldWhileRuns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:14:47.05319+00:00
-- url     : https://prove2.me/submissions/d1c46521-0063-44e7-b87b-88119938c92a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_QueryMachines_CombRuns
import Theorems.Thm_QueryMachines_QueryMachine_foldWhile_reaches
import Theorems.Thm_Groundwork_Stepped_foldWhile_reaches


set_option autoImplicit false
section
section
open QueryMachines
open Groundwork Finset QueryMachine
namespace QueryMachines
theorem _root_.solution : StFoldWhileRuns := fun _ _ _ _ _ _ _ _ _ _ _ _ c₀ _ a _ ho t Lq v Sx Sc Sm hM hx hc =>
  foldWhile_reaches ho t Lq v Sx Sc Sm (c₀ a) hM hx hc
end QueryMachines
