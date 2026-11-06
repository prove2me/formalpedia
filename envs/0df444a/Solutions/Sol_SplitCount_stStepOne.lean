-- Prove2me | solution 1 for SplitCount.stStepOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:34:25.455525+00:00
-- url     : https://prove2.me/submissions/cf23339e-a225-4220-8141-c2d5c7d4a307

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
import Theorems.Thm_SplitCount_stStepOneFor
import Theorems.Thm_SplitCount_stComputesZ
import Theorems.Thm_SplitCount_stCountIsNetworkMachine
import Theorems.Thm_Eight_ViaGrouping_CLIQUEp_within
import Theorems.Thm_Eight_ViaGrouping_two_le_levelK
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono


set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
namespace SplitCount
theorem _root_.solution : StStepOne := by
  intro δ' h0 h1 ℓ hK hE
  obtain ⟨A, hA⟩ := stComputesZ δ' h0 h1 (levelK ℓ) (CLIQUEp ℓ) (two_le_levelK ℓ) hK ((CLIQUEp_within ℓ).mono hE)
  rw [← stCountIsNetworkMachine ℓ] at hA
  exact stStepOneFor (COUNTp ℓ) δ' A h0.le hA
end SplitCount
