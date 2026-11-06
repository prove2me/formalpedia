-- Prove2me | solution 1 for P2M_Eight_ViaGrouping_corCircuits__of_02487e33d61e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:40:33.152135+00:00
-- url     : https://prove2.me/submissions/7b8cbd4f-6bf6-42af-9816-4204e32629e1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_ENP
import Definitions.Def_Eight_ViaGrouping_CorDefs2
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_CorENP
import Theorems.Thm_Eight_ViaGrouping_stAlg_from
import Theorems.Thm_CircuitLowerBound_stChain
import Theorems.Thm_CircuitLowerBound_stCode
import Theorems.Thm_CircuitLowerBound_stGreedy
import Theorems.Thm_CircuitLowerBound_stTab
import Theorems.Thm_CircuitLowerBound_stVars
import Theorems.Thm_P2M_CircuitLowerBound_corCircuits__of_9b88f614dd99
import Theorems.Thm_P2M_CircuitLowerBound_stENP__443f046b8760


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open ENP Groundwork Turing CircuitLowerBound
namespace Eight.ViaGrouping
theorem _root_.solution (hEng : StEngine) : ENP.CorCircuits' := CircuitLowerBound.corCircuits'_of stTab stCode stChain stVars stGreedy (stAlg_from hEng) stENP'
end Eight.ViaGrouping
