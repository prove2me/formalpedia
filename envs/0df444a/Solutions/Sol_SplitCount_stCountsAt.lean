-- Prove2me | solution 1 for SplitCount.stCountsAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:20:47.130148+00:00
-- url     : https://prove2.me/submissions/ba3ec53b-b243-4d77-bcf9-5a31c378ffb3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Definitions.Def_SplitCount_StepOne
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SplitCount_Suffices
import Definitions.Def_SplitCount_Cert
import Definitions.Def_SplitCount_Host
import Definitions.Def_CountKSat_Host
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_EndLemmas
import Definitions.Def_Eight_ViaGrouping_Alg
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Definitions.Def_SplitCount_Main
import Theorems.Thm_SplitCount_deltaPrime_facts
import Theorems.Thm_SplitCount_stStepOne
import Theorems.Thm_SplitCount_stSuffices
import Theorems.Thm_WidthK_InvK_step


set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal
namespace SplitCount
theorem _root_.solution : StCountsAt := by
  intro k hk δ hδ step Dd Bl Sk hsp ℓ hK hE
  obtain ⟨h0, h1, h2⟩ := deltaPrime_facts hδ (le_max_right k 3) Bl
  obtain ⟨A, hA⟩ := stStepOne _ h0 h1 ℓ hK hE
  exact stSuffices k hk δ hδ step Dd Bl Sk hsp (countThree ℓ) _ A h0.le h2 hA
end SplitCount
