-- Prove2me | solution 1 for Printed.stLevelTied_from
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:12:35.897207+00:00
-- url     : https://prove2.me/submissions/f2aa02f1-e021-4cb3-9010-a18b91d84ce5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelSentences
import Definitions.Def_Printed_LevelPoly
import Definitions.Def_Printed_GroupingPoly
import Definitions.Def_Printed_LevelFrom
import Theorems.Thm_Printed_stAskServes
import Theorems.Thm_Printed_stCliqueValue
import Theorems.Thm_Printed_stLevelTied_of
import Theorems.Thm_Printed_stOnProcedures
import Theorems.Thm_Value_stCliqueValue


set_option autoImplicit false
section
section
open Printed
namespace Printed
theorem _root_.solution (hG : StGroupingTied) : StLevelTied := stLevelTied_of stAskServes stCliqueValue hG stOnProcedures
end Printed
