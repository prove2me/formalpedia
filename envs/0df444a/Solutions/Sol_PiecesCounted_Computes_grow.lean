-- Prove2me | solution 1 for PiecesCounted.Computes.grow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:52:20.08788+00:00
-- url     : https://prove2.me/submissions/74c4239b-630c-4f8f-bfd1-8e7446e69d89

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_GeneralPieces_DefGenPieces_ToPure
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Basic
import Theorems.Thm_PiecesCounted_steps_le_of_le
import Theorems.Thm_PiecesCounted_room_le_of_le
import Theorems.Thm_PiecesCounted_oracle_eq_some
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono


set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg
namespace PiecesCounted
namespace Computes
theorem _root_.solution {Alg : Stepped (List Unit × Question) Answer} {D : Data} {c c' : ℕ} (h : Computes Alg D c) (hc : c ≤ c') : Computes Alg D c' :=
  fun g a hg => (h g a hg).mono (steps_le_of_le _ hc) (room_le_of_le (oracle_eq_some hg).1 hc)
end Computes
end PiecesCounted
