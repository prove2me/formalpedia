-- Prove2me | solution 1 for RecursionToBound.thmVariablesAForEveryMachine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:32:17.349289+00:00
-- url     : https://prove2.me/submissions/997e6e93-fa40-46dd-80e8-5e41ebbd64b7

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
import Theorems.Thm_RecursionToBound_countIsRight
import Theorems.Thm_RecursionToBound_countIsPolynomialTime
import Theorems.Thm_RecursionToBound_planFailsOnlyAboveN
import Theorems.Thm_RecursionToBound_thmVariablesAForEveryMachine_of
import Theorems.Thm_RecursionToBound_widthOnTheCode


set_option autoImplicit false
section
section
open RecursionToBound
namespace RecursionToBound
theorem _root_.solution : ThmVariablesAForEveryMachine :=
  thmVariablesAForEveryMachine_of countIsRight countIsPolynomialTime planFailsOnlyAboveN widthOnTheCode
end RecursionToBound
