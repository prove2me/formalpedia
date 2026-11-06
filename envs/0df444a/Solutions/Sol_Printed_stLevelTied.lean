-- Prove2me | solution 1 for Printed.stLevelTied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:21:07.865649+00:00
-- url     : https://prove2.me/submissions/b5a2f398-4ec4-429c-86bb-124d1a7896a4

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
import Theorems.Thm_Printed_stGroupingTied
import Theorems.Thm_Printed_stLevelTied_from


set_option autoImplicit false
section
section
open Printed
namespace Printed
theorem _root_.solution : StLevelTied := stLevelTied_from stGroupingTied
end Printed
