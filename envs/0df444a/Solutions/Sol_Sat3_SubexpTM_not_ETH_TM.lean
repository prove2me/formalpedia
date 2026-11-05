-- Prove2me | solution 1 for Sat3.SubexpTM.not_ETH_TM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:35:47.754184+00:00
-- url     : https://prove2.me/submissions/7d10b0c5-c679-4ae3-9e64-75aab651b4e9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_ToTuring_EndLemmas
import Definitions.Def_PaddedDescent_RateLemmas
import Theorems.Thm_Sat3_SubexpTM_inTimeTM
import Theorems.Thm_Sat3_not_ETH_TM_iff


set_option autoImplicit false
section
section
open Sat3
open Turing
open scoped NNReal ENNReal
namespace Sat3
namespace SubexpTM
theorem _root_.solution (h : SubexpTM) : ¬ ETH_TM := not_ETH_TM_iff.2 fun _ hδ => h.inTimeTM hδ
end SubexpTM
end Sat3
