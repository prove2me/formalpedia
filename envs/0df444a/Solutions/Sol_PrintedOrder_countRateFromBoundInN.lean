-- Prove2me | solution 1 for PrintedOrder.countRateFromBoundInN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:24:07.198168+00:00
-- url     : https://prove2.me/submissions/d64d4898-98aa-4f89-ad88-e29340bfda37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedOrder_Defs
import Definitions.Def_ThmCount_Main
import Definitions.Def_RecursionWithPieces_Forms
import Definitions.Def_PrintedOrder_Close
import Theorems.Thm_RecursionWithPieces_Forms_thmVariablesB
import Theorems.Thm_ThmCount_stTheorem


set_option autoImplicit false
section
section
open PrintedOrder
namespace PrintedOrder
theorem _root_.solution : CountRateFromBoundInN := ThmCount.stTheorem RecursionWithPieces.Forms.thmVariablesB
end PrintedOrder
