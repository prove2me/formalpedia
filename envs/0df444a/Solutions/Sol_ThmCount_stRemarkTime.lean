-- Prove2me | solution 1 for ThmCount.stRemarkTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:28:50.631852+00:00
-- url     : https://prove2.me/submissions/189f174b-6b2a-43fc-8c32-bd6e62b233c7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_ThmCount_Main
import Definitions.Def_RecursionWithPieces_Forms
import Definitions.Def_ThmCount_Remark
import Theorems.Thm_RecursionWithPieces_Forms_thmVariablesB
import Theorems.Thm_ThmCount_stRemarkTime_of


set_option autoImplicit false
section
section
open ThmCount
namespace ThmCount
theorem _root_.solution : StRemarkTime := stRemarkTime_of RecursionWithPieces.Forms.thmVariablesB
end ThmCount
