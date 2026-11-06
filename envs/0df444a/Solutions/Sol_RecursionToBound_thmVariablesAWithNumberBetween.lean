-- Prove2me | solution 1 for RecursionToBound.thmVariablesAWithNumberBetween
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:39:14.12227+00:00
-- url     : https://prove2.me/submissions/5127aeef-95ba-4f41-9940-a801096af71d

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
import Theorems.Thm_RecursionToBound_thmVariablesAForEveryMachine
import Theorems.Thm_RecursionToBound_thmVariablesAWithNumberBetween_of


set_option autoImplicit false
section
section
open RecursionToBound
namespace RecursionToBound
theorem _root_.solution : ThmVariablesAWithNumberBetween := thmVariablesAWithNumberBetween_of thmVariablesAForEveryMachine
end RecursionToBound
