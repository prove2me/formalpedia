-- Prove2me | solution 1 for Value.stValueEqualsZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:07:09.690896+00:00
-- url     : https://prove2.me/submissions/8269cf87-6528-45c8-89ea-d30b13d250b6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Clique
import Definitions.Def_Value_Joint
import Definitions.Def_Value_End
import Theorems.Thm_Value_stValueEqualsZOf
import Theorems.Thm_Value_stCliqueValue
import Theorems.Thm_Value_stJointSum
import Theorems.Thm_Value_stSumOut


set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
namespace Value
theorem _root_.solution : StValueEqualsZ := stValueEqualsZOf stCliqueValue stJointSum stSumOut
end Value
