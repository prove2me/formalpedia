-- Prove2me | solution 1 for P2M_CircuitLowerBound_stENP__443f046b8760
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:31:28.105557+00:00
-- url     : https://prove2.me/submissions/4dd4aba2-43f2-4a25-a6c8-ab14a63e5d78

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Main
import Definitions.Def_CircuitLowerBound_Small
import Definitions.Def_CircuitLowerBound_Tab_Complete
import Definitions.Def_CircuitLowerBound_Tab_Pack
import Definitions.Def_CircuitLowerBound_Tab_Table
import Definitions.Def_CircuitLowerBound_Tab_Glue
import Definitions.Def_CircuitLowerBound_Cert_TabF
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Definitions.Def_CircuitLowerBound_Circ_Norm
import Definitions.Def_CircuitLowerBound_Circ_Form
import Definitions.Def_CircuitLowerBound_Alg_Time
import Definitions.Def_CircuitLowerBound_ENP_Restart
import Definitions.Def_CircuitLowerBound_Oracle_Restart
import Definitions.Def_CircuitLowerBound_Closed
import Theorems.Thm_CircuitLowerBound_stCertSched
import Theorems.Thm_CircuitLowerBound_stCertTabF
import Theorems.Thm_CircuitLowerBound_stFlip
import Theorems.Thm_P2M_CircuitLowerBound_stENP__of_10b343dee6a6


set_option autoImplicit false
section
section
open CircuitLowerBound
namespace CircuitLowerBound
theorem _root_.solution : StENP' := stENP'_of stCertSched stCertTabF stFlip
end CircuitLowerBound
