-- Prove2me | solution 1 for SplitSat.stTiedTM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:58:11.717434+00:00
-- url     : https://prove2.me/submissions/51cb01ce-f615-4d7d-9e07-e50826541b72

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
import Theorems.Thm_SplitSat_stSATsplit
import Theorems.Thm_SplitSat_decidesTM_of_simulates
import Theorems.Thm_SplitSat_decides_mono
import Theorems.Thm_SplitSat_exists_simulates


set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight.ViaGrouping
open scoped NNReal ENNReal
namespace SplitSat
theorem _root_.solution : StTiedTM := fun k hk δ hδ => by
  obtain ⟨τ, ℓ₃, τ₃, hp, c, hd⟩ := stSATsplit k hk (δ / 2) (by positivity)
  obtain ⟨M, q, hfin, hs⟩ := exists_simulates _ hp
  obtain ⟨C, hcC, hTM⟩ := decidesTM_of_simulates hδ hs hd
  exact ⟨τ, ℓ₃, τ₃, M, C, q, hfin, hp, decides_mono (by linarith) hcC hd, hs, hTM⟩
end SplitSat
