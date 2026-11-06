-- Prove2me | solution 1 for Printed.stGroupingTied_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:14:15.710479+00:00
-- url     : https://prove2.me/submissions/667a5a91-ff79-4f25-974a-0edfdadc01c4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_GroupingProcs
import Definitions.Def_Printed_GroupingRun
import Definitions.Def_Printed_GroupingPoly
import Mathlib.Tactic
import Definitions.Def_Printed_Grouping
import Theorems.Thm_Printed_stEntryCost
import Theorems.Thm_Printed_stGroupingTiedOf
import Theorems.Thm_QueryMachines_stSubst


set_option autoImplicit false
section
section
open Printed
open QueryMachines
namespace Printed
theorem _root_.solution (hS : Eight.ViaGrouping.StSearch) (hStops : Exits.StSearchStops) (hV : Value.StValueEqualsZ) : StGroupingTied := stGroupingTiedOf hS hStops stEntryCost hV stSubst
end Printed
