-- Prove2me | solution 1 for SplitSat.stTiedThreeTM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:43:01.980231+00:00
-- url     : https://prove2.me/submissions/dcd4206d-c833-4a4b-acc7-355b77ed6eb8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Cert
import Definitions.Def_SplitSat_Reader
import Definitions.Def_SplitSat_Procedure
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_SparsificationLemma_TreeWalk_Walk
import Definitions.Def_ThreeSatPrinted_ThmEveryDelta
import Definitions.Def_WidthK_Top_EndLemmas
import Mathlib.Tactic
import Definitions.Def_SplitSat_Main
import Theorems.Thm_SplitSat_decidesTM_of_simulates
import Theorems.Thm_SplitSat_decides_mono
import Theorems.Thm_SplitSat_exists_simulates
import Theorems.Thm_ThreeSatPrinted_algPseudocode_decides_viaC


set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight.ViaGrouping
open scoped NNReal ENNReal
namespace SplitSat
theorem _root_.solution : StTiedThreeTM := fun δ hδ => by
  obtain ⟨ℓ, τ, -, hp, c, hd⟩ := ThreeSatPrinted.algPseudocode_decides_viaC (δ := δ / 2) (by positivity)
  have hd' : Decides (ThreeSatPrinted.SATCp ℓ τ) 3 (δ / 2) c := hd
  obtain ⟨M, q, hfin, hs⟩ := exists_simulates _ hp
  obtain ⟨C, hcC, hTM⟩ := decidesTM_of_simulates hδ hs hd'
  exact ⟨ℓ, τ, M, C, q, hfin, hp, decides_mono (by linarith) hcC hd', hs, hTM⟩
end SplitSat
