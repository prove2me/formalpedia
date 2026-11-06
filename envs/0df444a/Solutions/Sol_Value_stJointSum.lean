-- Prove2me | solution 1 for Value.stJointSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:57:55.58911+00:00
-- url     : https://prove2.me/submissions/82bf1ea1-13f5-4b9f-b72a-e938c781e1a8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Blocks
import Definitions.Def_Value_Sums
import Definitions.Def_Value_Joint
import Theorems.Thm_Value_stJointSumOf
import Theorems.Thm_Value_stAppendedZero
import Theorems.Thm_Value_stBlocks
import Theorems.Thm_Value_stSameBlock
import Theorems.Thm_Value_stSumsInside


set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
variable {C : Type} [HasSize C] {g K : ℕ}
namespace Value
theorem _root_.solution : StJointSum := stJointSumOf stSameBlock stAppendedZero stBlocks stSumsInside
end Value
