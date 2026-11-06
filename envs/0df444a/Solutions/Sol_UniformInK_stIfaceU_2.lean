-- Prove2me | solution 2 for UniformInK.stIfaceU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:08:01.855251+00:00
-- url     : https://prove2.me/submissions/b99d8bd3-cb4c-4425-a2d6-dec662d68963

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_UniformInK_Spars_Step
import Definitions.Def_UniformInK_Spars_Bound
import Definitions.Def_UniformInK_Spars_Thresholds
import Definitions.Def_UniformInK_Spars_Iface
import Definitions.Def_UniformInK_Spars_Main
import Theorems.Thm_UniformInK_ifaceU
import Theorems.Thm_UniformInK_stBetaSumU
import Theorems.Thm_UniformInK_stNodeBoundU
import Theorems.Thm_UniformInK_stNodeRootU
import Theorems.Thm_UniformInK_stNodeStepU
import Theorems.Thm_UniformInK_stThrU


set_option autoImplicit false
section
section
open UniformInK
namespace UniformInK
theorem _root_.solution : StIfaceU := ifaceU stNodeRootU stNodeStepU stNodeBoundU stThrU stBetaSumU
end UniformInK
