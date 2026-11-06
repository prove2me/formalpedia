-- Prove2me | solution 1 for SplitCount.stComputesZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:51:06.685773+00:00
-- url     : https://prove2.me/submissions/e2a2c319-dc49-46f1-a84b-17967aeb4aa4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_Occ_Main
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_ViaGrouping_LemGrouping
import Definitions.Def_Eight_ViaGrouping_Alg
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_SplitCount_StepOne
import Theorems.Thm_Eight_ViaGrouping_count_cost_of
import Theorems.Thm_Eight_ViaGrouping_stLemGrouping


set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
namespace SplitCount
theorem _root_.solution : StComputesZ := by
  intro δ' h0 h1 K E hK2 hK hE
  have hg : 0 < 3 * K ^ 8 := by
    have : 0 < K := by omega
    positivity
  exact ViaGrouping.count_cost_of h0 h1 hg hK (ViaGrouping.stLemGrouping K (δ' / 12) E hK2 (by positivity) hE)
end SplitCount
