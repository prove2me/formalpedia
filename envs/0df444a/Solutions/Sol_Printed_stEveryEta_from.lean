-- Prove2me | solution 1 for Printed.stEveryEta_from
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:48:35.968099+00:00
-- url     : https://prove2.me/submissions/a01fbf8d-ae63-482a-a932-cdd09af968b9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelSentences
import Definitions.Def_Printed_LevelPoly
import Definitions.Def_Printed_GroupingPoly
import Definitions.Def_Printed_LevelFrom
import Theorems.Thm_Printed_eStarZero_from
import Theorems.Thm_Printed_stEveryEta_of


set_option autoImplicit false
section
section
open Printed
namespace Printed
theorem _root_.solution (hG : StGroupingTied) : StEveryEta := stEveryEta_of (eStarZero_from hG)
end Printed
