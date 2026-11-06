-- Prove2me | solution 1 for Printed.stOnProcedures
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:29:30.879491+00:00
-- url     : https://prove2.me/submissions/0325560e-97a0-456c-8912-fbd176b4473c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingProcs
import Theorems.Thm_Printed_inputOf_eq
import Theorems.Thm_Printed_answerOf_runs
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_Stepped_mapIn_runs
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_cap_eq
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_QueryMachines_QueryMachine_sum_map_const
import Theorems.Thm_QueryMachines_stPlug
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight Eight.SecNetworks QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution : StOnProcedures := by
  intro NM C₁ g K e hNM C _ Np c N P B τ S hN
  obtain ⟨T, ⟨own, L, hrun, hle⟩, hT⟩ := hNM N P B τ hN.is hN.τ_pos
  have hτ := hN.τ_pos
  have hp := stPlug _ _ _ _ _ NM (answerOf Np) (netOracle N) c (netInput N P B) own _ (S + 3) L N.value (fun _ => τ) hrun fun x _ v hv => answerOf_runs hN.given hv
  rw [sum_map_const] at hle hp
  have hin : inputOf g (Np.P c) (Np.B c) (Np.len c) (Np.cap c) = netInput N P B := by
    rw [hN.given.P_eq, hN.given.B_eq]
    exact inputOf_eq N P B _ _ hN.given.len_eq hN.given.cap_eq
  refine ⟨own + L.length * (τ + 2), ?_, ?_⟩
  · refine Stepped.Runs.mono (Stepped.mapIn_runs ?_) le_rfl (le_refl _)
    rw [hin]
    exact hp.mono le_rfl (by omega)
  · have h1 : L.length ≤ L.length * τ := Nat.le_mul_of_pos_right _ hτ
    have h2 : own + L.length * (τ + 2) ≤ 3 * T := by
      rw [Nat.mul_add]
      omega
    have h3 : ((own + L.length * (τ + 2) : ℕ) : ℝ) ≤ 3 * (T : ℝ) := by exact_mod_cast h2
    refine h3.trans ?_
    linarith
end Printed
