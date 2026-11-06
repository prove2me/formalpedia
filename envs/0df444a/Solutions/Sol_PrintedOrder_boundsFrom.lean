-- Prove2me | solution 1 for PrintedOrder.boundsFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:12:24.899054+00:00
-- url     : https://prove2.me/submissions/7fd62d02-4d69-4fc0-970f-e65783194a0f

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
import Theorems.Thm_CountKSat_stProgC
import Theorems.Thm_CountKSat_stRootCount
import Theorems.Thm_CountKSat_stSumLeaves
import Theorems.Thm_SplitCount_sparsifiesPlain_of
import Theorems.Thm_WidthK_stExistsTau


set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ SplitCount
open scoped NNReal
namespace PrintedOrder
theorem _root_.solution : StStepAdds → StBounds := fun hS k _ hε => by
  obtain ⟨τ, -, h4, hτ⟩ := WidthK.stExistsTau k 0 _ hε
  have hsp := sparsifiesPlain_of (stProgC hS stRootCount stSumLeaves τ k _ (by omega) hτ)
  refine ⟨τ, WidthK.bsum τ k, WidthK.leafC τ k + k * WidthK.bsum τ k + 1, 2 ^ k + k * WidthK.bsum τ k + 1, fun n ψ hψ => ?_⟩
  obtain ⟨t1, t2, -, t4⟩ := hsp n ψ hψ
  exact ⟨t1, t2, t4⟩
end PrintedOrder
