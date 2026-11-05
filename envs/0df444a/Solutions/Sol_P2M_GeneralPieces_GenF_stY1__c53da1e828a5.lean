-- Prove2me | solution 1 for P2M_GeneralPieces_GenF_stY1__c53da1e828a5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:39.02752+00:00
-- url     : https://prove2.me/submissions/f3354a16-b44a-4ac3-b73c-01ead765c813

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Y
import Definitions.Def_Eth_16a5ce4_GeneralPieces_GenF_Y2_Definitions
import Definitions.Def_GeneralPieces_GenF_YY
import Definitions.Def_GeneralPieces_GenF_YMain
import Theorems.Thm_GeneralPieces_GenF_Y2
import Theorems.Thm_GeneralPieces_GenF_pderiv_xi_outer


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
namespace GeneralPieces.GenF
theorem _root_.solution : StY1' := fun rd n σ' => pderiv_xi_outer rd n σ'
end GeneralPieces.GenF
