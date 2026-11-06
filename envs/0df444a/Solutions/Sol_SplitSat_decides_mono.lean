-- Prove2me | solution 1 for SplitSat.decides_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:36:06.213963+00:00
-- url     : https://prove2.me/submissions/4f3d1de6-16e2-4a8d-be25-2b7c6e4a5ae7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_CountKSat_Host
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_SplitSat_Simulate
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
open SplitSat
open Groundwork Groundwork.Prog Paper CountKSat Eight.ViaGrouping
namespace SplitSat
theorem _root_.solution {M : StepMachine (List Bool) Bool} {k : ℕ} {δ δ' : ℝ} {c c' : ℕ} (hδ : δ ≤ δ') (hc : c ≤ c') (h : Decides M k δ c) :
    Decides M k δ' c' := by
  intro n φ h3
  obtain ⟨T, b, r, hb, hT⟩ := h n φ h3
  refine ⟨T, b, r.mono le_rfl (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hc)), hb, hT.trans ?_⟩
  have h1 : (c : ℝ) ≤ c' := by exact_mod_cast hc
  have h2 : (2 : ℝ) ^ (δ * n) ≤ (2 : ℝ) ^ (δ' * n) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg n))
  exact mul_le_mul h1 h2 (by positivity) (Nat.cast_nonneg _)
end SplitSat
