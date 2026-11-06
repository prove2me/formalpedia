-- Prove2me | solution 1 for Printed.stGroupingTied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:36:03.935331+00:00
-- url     : https://prove2.me/submissions/833920f7-77ea-46a1-ae21-1aecaeae1cdd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Proof
import Definitions.Def_Printed_LevelFrom
import Definitions.Def_Printed_Grouping
import Definitions.Def_Variance_Grouping
import Definitions.Def_Exits_End
import Definitions.Def_Value_End
import Definitions.Def_Suffices_Main
import Definitions.Def_Enumerate_Enumeration
import Definitions.Def_Printed_End
import Theorems.Thm_Eight_ViaGrouping_stSearch
import Theorems.Thm_Exits_stSearchStops
import Theorems.Thm_Printed_stGroupingTied_of
import Theorems.Thm_Value_stValueEqualsZ
import Theorems.Thm_Variance_stSearch


set_option autoImplicit false
section
section
open Printed
namespace Printed
theorem _root_.solution : StGroupingTied := stGroupingTied_of Variance.stSearch Exits.stSearchStops Value.stValueEqualsZ
end Printed
