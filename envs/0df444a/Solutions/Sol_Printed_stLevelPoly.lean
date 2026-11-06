-- Prove2me | solution 1 for Printed.stLevelPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:26:53.600015+00:00
-- url     : https://prove2.me/submissions/3cd6664b-4c32-49bc-9533-5f56267f4947

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelSentences
import Definitions.Def_Printed_LevelPoly
import Definitions.Def_Printed_GroupingPoly
import Definitions.Def_Printed_LevelFrom
import Theorems.Thm_Printed_stGroupingPoly
import Theorems.Thm_Printed_stLevelPoly_of


set_option autoImplicit false
section
section
open Printed
namespace Printed
theorem _root_.solution : StLevelPoly := stLevelPoly_of stGroupingPoly
end Printed
