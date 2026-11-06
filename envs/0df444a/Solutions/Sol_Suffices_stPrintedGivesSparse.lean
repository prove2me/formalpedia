-- Prove2me | solution 1 for Suffices.stPrintedGivesSparse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:46:32.987894+00:00
-- url     : https://prove2.me/submissions/66968d1b-954e-4d22-ade2-cca4a360aa9d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Loop
import Definitions.Def_Suffices_Total
import Definitions.Def_Exits_Poly
import Definitions.Def_CountKSat_InOut
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Suffices_Main
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono


set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Paper SparsificationLemma Enumerate Exits
namespace Suffices
theorem _root_.solution : StPrintedGivesSparse := by
  intro δ M S h
  refine ⟨h.1, fun Mc A hMc => h.2 Mc A fun n Φ h3 _ => ?_⟩
  obtain ⟨T, v, r, hv, hT⟩ := hMc Φ fun C hC => (h3 C hC).2.1
  refine ⟨T, v, r.mono le_rfl (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_add_right _ _) A)), hv, hT.trans ?_⟩
  have h0 : (0 : ℝ) ≤ (A : ℝ) * ((n : ℝ) + 1) ^ A := by positivity
  linarith
end Suffices
