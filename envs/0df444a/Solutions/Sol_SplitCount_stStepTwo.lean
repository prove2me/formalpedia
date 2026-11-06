-- Prove2me | solution 1 for SplitCount.stStepTwo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:58:38.334532+00:00
-- url     : https://prove2.me/submissions/ed3c6476-59a1-4bb8-a7a7-d648913ef458

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_CountKSat_ProgC
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_Walk
import Mathlib.Tactic.Tauto
import Definitions.Def_SplitCount_Tree
import Theorems.Thm_SplitCount_sparsifiesPlain_of
import Theorems.Thm_CountKSat_stProgC
import Theorems.Thm_CountKSat_stRootCount
import Theorems.Thm_CountKSat_stStepCount
import Theorems.Thm_CountKSat_stSumLeaves
import Theorems.Thm_WidthK_stExistsTau


set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight Eight.Width
namespace SplitCount
theorem _root_.solution : StStepTwo := fun k _ hε => by
  obtain ⟨τ, -, h4, hτ⟩ := WidthK.stExistsTau k 0 _ hε
  exact ⟨τ, _, _, _, sparsifiesPlain_of (stProgC stStepCount stRootCount stSumLeaves τ k _ (by omega) hτ)⟩
end SplitCount
