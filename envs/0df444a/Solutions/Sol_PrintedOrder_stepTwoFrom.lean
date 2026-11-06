-- Prove2me | solution 1 for PrintedOrder.stepTwoFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:38:52.783494+00:00
-- url     : https://prove2.me/submissions/92d8816f-da3e-405e-bdd6-d90aa7fbb414

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedOrder_Defs
import Definitions.Def_PrintedOrder_AddUp
import Definitions.Def_SplitCount_Main
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SplitCount_Cert
import Definitions.Def_SplitCount_Host
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Definitions.Def_CountKSat_Host
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_EndLemmas
import Definitions.Def_Eight_ViaGrouping_Alg
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_PrintedOrder_Counting

set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ SplitCount
open scoped NNReal
namespace PrintedOrder
theorem _root_.solution : StTreeAddsUp → StBounds → SplitCount.StStepTwo := fun hT hB k ε hε => by
  obtain ⟨τ, Dd, Bl, Sk, h⟩ := hB k ε hε
  refine ⟨τ, Dd, Bl, Sk, fun n ψ hψ => ?_⟩
  obtain ⟨t1, t2, t4⟩ := h n ψ hψ
  exact ⟨t1, t2, hT _ k _ n ψ, t4⟩
end PrintedOrder
