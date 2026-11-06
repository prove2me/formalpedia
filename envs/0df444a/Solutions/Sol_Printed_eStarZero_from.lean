-- Prove2me | solution 1 for Printed.eStarZero_from
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:41:54.06019+00:00
-- url     : https://prove2.me/submissions/80029f72-7cb5-4364-aff4-a48624f7c4db

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_LevelSentences
import Definitions.Def_Printed_LevelPoly
import Definitions.Def_Printed_GroupingPoly
import Definitions.Def_Printed_LevelFrom
import Theorems.Thm_Printed_levelProposition_from
import Theorems.Thm_Printed_eStarZero_of


set_option autoImplicit false
section
section
open Printed
namespace Printed
theorem _root_.solution (hG : StGroupingTied) : EStarZero := eStarZero_of (levelProposition_from hG)
end Printed
