-- Prove2me | solution 1 for Sat3Graph.decidesColor_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:48:32.713007+00:00
-- url     : https://prove2.me/submissions/16f76e13-93f5-4cce-a39d-442064a63fb5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_GraphProblems_Read
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Host
import Theorems.Thm_Sat3Graph_size_mono
import Theorems.Thm_Sat3Graph_time_mono
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Paper_Achievable_mono


set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog GraphProblems Paper SplitSat
namespace Sat3Graph
theorem _root_.solution {Ms : StepMachine (List Bool) Bool} {k : ℕ} {δ δ' : ℝ} {c c' : ℕ}
    (hδ : δ ≤ δ') (hc : c ≤ c') (h : DecidesColor Ms k δ c) : DecidesColor Ms k δ' c' := by
  intro n G
  obtain ⟨T, b, r, hb, hT⟩ := h n G
  exact ⟨T, b, r.mono le_rfl (size_mono hc n), hb, hT.trans (time_mono hδ hc n)⟩
end Sat3Graph
