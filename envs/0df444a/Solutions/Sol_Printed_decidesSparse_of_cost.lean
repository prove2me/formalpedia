-- Prove2me | solution 1 for Printed.decidesSparse_of_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:13:27.190648+00:00
-- url     : https://prove2.me/submissions/5e3b43c9-6240-43a3-9c17-3612a7ba53b8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Count
import Mathlib.Tactic
import Definitions.Def_Printed_Proof
import Theorems.Thm_Eight_numSat_pos_iff
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_Printed_AchievedBy_mono
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Printed
open Groundwork Groundwork.Prog Eight Eight.SecNetworks Paper QueryMachines
namespace Printed
theorem _root_.solution {δ' : ℝ} {M A : ℕ} {Mc : StepMachine Formula ℤ}
    (h : ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) → ∃ T : ℕ, Mc.Runs Φ T (A * size Φ ^ A) (numSat Φ) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length)) :
    Suffices.DecidesSparse δ' M Mc A := by
  intro n Φ hΦ _
  obtain ⟨T, hr, hT⟩ := h Φ fun C hC => (hΦ C hC).2.1
  exact ⟨T, _, hr.mono le_rfl (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_add_right _ _) _)), by rw [Nat.cast_pos]; exact Eight.numSat_pos_iff Φ,
    hT.trans (le_add_of_nonneg_right (by positivity))⟩
end Printed
