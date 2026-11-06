-- Prove2me | solution 1 for Printed.stBothNetworks_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:36:46.017838+00:00
-- url     : https://prove2.me/submissions/088bb2fd-d7a5-4509-92b9-e5184869bd6f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_CodingDefs
import Definitions.Def_Printed_Achievable
import Definitions.Def_Printed_GroupingProcs
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Mathlib.Tactic
import Definitions.Def_Printed_LevelNetworks
import Theorems.Thm_Printed_poly_absorb
import Theorems.Thm_Printed_grid_isNetwork_of
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_PaddedDescent_F_cap_eq
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_Printed_answerOf_runs
import Theorems.Thm_Printed_answer_close
import Theorems.Thm_Printed_inputOf_eq
import Theorems.Thm_Printed_length_unary
import Theorems.Thm_Printed_size_unary
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_QueryMachines_stClose
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
attribute [local simp] Groundwork.size_prod



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution (hA : StAskServes) : StBothNetworks := by
  intro g hg
  obtain ⟨a, ha⟩ := grid_isNetwork_of hA g hg
  obtain ⟨a', ha'⟩ := poly_absorb a (size (g * g) + 4 * (g * g) + 9)
  refine ⟨a', fun tr lam B W y hl hB hW hy => ?_⟩
  have h := ha tr (unary lam, unary B) lam B W y (length_unary lam) (length_unary B) hl hW hy
  refine ⟨h.is, ?_, fun x v hx => ?_⟩
  · rw [show (gridProcs g tr).P ((unary lam, unary B), y) = g ^ 3 * lam from h.given.P_eq, show (gridProcs g tr).B ((unary lam, unary B), y) = g * B + g ^ 2 * lam + 1 from h.given.B_eq]
    cases tr
    · exact inputOf_eq (g := g) (levelNetP g false lam y (listTables (g * g) W)) _ _ _ _ h.given.len_eq h.given.cap_eq
    · exact inputOf_eq (g := g) (levelNetP g true lam y (listTables (g * g) W)) _ _ _ _ h.given.len_eq h.given.cap_eq
  · have hr := answerOf_runs h.given hx
    rw [← answer_close] at hr
    refine ((stClose _ _ _ _ _ _ _ _ _ _).1 hr).mono ?_ ?_
    · exact le_trans (Nat.le_add_right _ _) (ha' (B + lam) (B + lam) (by omega) (by omega))
    · obtain ⟨X, hX⟩ : ∃ X, X = size (unary lam, unary B) + B + lam := ⟨_, rfl⟩
      have hs : size (unary lam, unary B) = 2 * lam + 1 + (2 * B + 1) := by rw [size_prod, size_unary, size_unary]
      have h0 := ha' X (B + lam) (by omega) (by omega)
      have h1 : size (g * g) ≤ size (g * g) * X := Nat.le_mul_of_pos_right _ (by omega)
      have h2 : g * g * (2 * lam + 2) ≤ g * g * (4 * X) := Nat.mul_le_mul_left _ (by omega)
      have e : (size (g * g) + 4 * (g * g) + 9) * X = size (g * g) * X + g * g * (4 * X) + 9 * X := by ring
      rw [← hX]
      omega
end Printed
