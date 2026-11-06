-- Prove2me | solution 1 for Value.stValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:15:03.089109+00:00
-- url     : https://prove2.me/submissions/290d40bd-f6c0-4436-9b98-f8d5d5ebce17

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Clique
import Definitions.Def_Value_Joint
import Definitions.Def_Value_End
import Theorems.Thm_Value_stValueEqualsZ
import Theorems.Thm_Value_stValueOf
import Theorems.Thm_Value_stCliqueValue


set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
namespace Value
theorem _root_.solution : Eight.ViaGrouping.StValue := stValueOf stCliqueValue stValueEqualsZ
end Value
