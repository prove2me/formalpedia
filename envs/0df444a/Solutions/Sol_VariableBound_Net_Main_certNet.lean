-- Prove2me | solution 1 for VariableBound.Net.Main.certNet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:41:02.667266+00:00
-- url     : https://prove2.me/submissions/47b2078f-515a-4ea6-8684-5b72490e2114

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Rank
import Definitions.Def_VariableBound_Net_CertRank
import Definitions.Def_VariableBound_Net_Val
import Definitions.Def_VariableBound_Net_Prof
import Definitions.Def_VariableBound_Net_Tuples
import Definitions.Def_VariableBound_Net_Total
import Definitions.Def_VariableBound_Net_SizeU
import Definitions.Def_VariableBound_Net_SizeB
import Definitions.Def_VariableBound_Net_SizeP
import Definitions.Def_VariableBound_Net_SizeSmall
import Definitions.Def_VariableBound_Net_Fit
import Definitions.Def_VariableBound_Net_Ev
import Definitions.Def_VariableBound_Net_CertNet
import Definitions.Def_VariableBound_Net_CertEv
import Definitions.Def_VariableBound_StepParity
import Definitions.Def_VariableBound_Params_Ineq
import Definitions.Def_ClauseBound_Alg_TopNet
import Definitions.Def_ClauseBound_Alg_CertTopNet
import Definitions.Def_PaddedDescent_Col_CertG
import Definitions.Def_VariableBound_Net_Main
import Theorems.Thm_VariableBound_Net_Main_certRank
import Theorems.Thm_VariableBound_Net_stCertNet


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Main
namespace VariableBound.Net.Main
theorem _root_.solution : StCertNet := stCertNet certRank
end VariableBound.Net.Main
