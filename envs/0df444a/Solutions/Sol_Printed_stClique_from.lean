-- Prove2me | solution 1 for Printed.stClique_from
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:34:08.291661+00:00
-- url     : https://prove2.me/submissions/2549def3-8085-4ac2-9a1a-3e2ae5992c28

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelSentences
import Definitions.Def_Printed_LevelPoly
import Definitions.Def_Printed_GroupingPoly
import Definitions.Def_Printed_LevelFrom
import Theorems.Thm_Printed_stLevelPoly
import Theorems.Thm_Printed_stLevelTied_from
import Theorems.Thm_Printed_stBrute
import Theorems.Thm_Printed_stClique_of


set_option autoImplicit false
section
section
open Printed
namespace Printed
theorem _root_.solution (hG : StGroupingTied) : StClique := stClique_of stBrute (stLevelTied_from hG) stLevelPoly
end Printed
