-- Prove2me | solution 1 for PrintedOrder.engineCountsFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:30:11.454057+00:00
-- url     : https://prove2.me/submissions/0365f91a-576d-4548-8a75-5c7f2004b896

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
import Theorems.Thm_CountKSat_Poly_certStepC
import Theorems.Thm_Eight_Level_exists_level
import Theorems.Thm_Eight_ViaGrouping_COUNTp_polyTimeSteps
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SplitCount_deltaPrime_facts
import Theorems.Thm_SplitCount_stCert
import Theorems.Thm_SplitCount_stCountsAt


set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ SplitCount
open scoped NNReal
namespace PrintedOrder
theorem _root_.solution (h2 : SplitCount.StStepTwo) : StEngineCounts := by
  intro k hk δ hδ
  obtain ⟨τ, Dd, Bl, Sk, hsp⟩ := h2 k (δ / 3) (by positivity)
  obtain ⟨h0, -, -⟩ := deltaPrime_facts hδ (le_max_right k 3) Bl
  obtain ⟨ℓ, a1, a2⟩ := Level.exists_level (η := deltaPrime δ (max k 3) Bl / 12) (by positivity) ⌈72 / deltaPrime δ (max k 3) Bl⌉₊
  exact ⟨ℓ, τ, SplitCount.stCert.2 _ _ (Poly.certStepC _ k) (SplitCount.stCert.1 _ (COUNTp_polyTimeSteps ℓ)),
    stCountsAt k hk δ hδ _ Dd Bl Sk hsp ℓ ((Nat.le_ceil _).trans (by exact_mod_cast a1)) a2⟩
end PrintedOrder
