-- Prove2me | solution 1 for PrintedOrder.hostedFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:44:11.538519+00:00
-- url     : https://prove2.me/submissions/9985c1de-5705-4049-b969-d5fd5bb32790

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PrintedOrder_Defs
import Definitions.Def_SplitSat_Main
import Definitions.Def_SplitSat_Procedure
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_WidthK_Top_EndLemmas
import Mathlib.Tactic
import Definitions.Def_PrintedOrder_Deciding
import Theorems.Thm_SplitSat_decidesTM_of_simulates
import Theorems.Thm_SplitSat_decides_mono
import Theorems.Thm_SplitSat_exists_simulates


set_option autoImplicit false
section
section
open PrintedOrder
open Groundwork Groundwork.Prog Paper Eight.ViaGrouping SplitSat
open scoped NNReal ENNReal
namespace PrintedOrder
theorem _root_.solution : SplitSat.StImplication → StHosted := fun hI Ds hDs k hk δ hδ => by
  obtain ⟨τ, δ₃, h0, hp, c, hd⟩ := hI Ds hDs k hk (δ / 2) (by positivity)
  obtain ⟨M, q, hfin, hs⟩ := exists_simulates _ hp
  obtain ⟨C, hcC, hTM⟩ := decidesTM_of_simulates hδ hs hd
  exact ⟨τ, δ₃, M, C, q, h0, hfin, hp, decides_mono (by linarith) hcC hd, hs, hTM⟩
end PrintedOrder
