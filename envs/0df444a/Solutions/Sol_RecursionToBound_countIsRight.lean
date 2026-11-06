-- Prove2me | solution 1 for RecursionToBound.countIsRight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:28:09.971208+00:00
-- url     : https://prove2.me/submissions/82add22b-3c75-41e6-802c-f71448380a18

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_RecursionToBound_OneOutput
import Definitions.Def_RecursionToBound_Exponent
import Definitions.Def_RecursionToBound_Cert_Top
import Definitions.Def_RecursionToBound_Guard
import Definitions.Def_RecursionToBound_Tree
import Definitions.Def_RecursionToBound_Correct
import Definitions.Def_RecursionToBound_End
import Definitions.Def_RecursionToBound_Main
import Theorems.Thm_RecursionToBound_countIsRight_of
import Theorems.Thm_RecursionToBound_cutOffIsIdle
import Theorems.Thm_RecursionToBound_outputsAreWithinTheSetting
import Theorems.Thm_RecursionToBound_planFailsOnlyAboveN


set_option autoImplicit false
section
section
open RecursionToBound
namespace RecursionToBound
theorem _root_.solution : CountIsRight := countIsRight_of outputsAreWithinTheSetting cutOffIsIdle planFailsOnlyAboveN
end RecursionToBound
