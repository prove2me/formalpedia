-- Prove2me | solution 1 for VariableBound.Ineq.large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:58:36.921756+00:00
-- url     : https://prove2.me/submissions/1c9b6296-a699-410e-9392-2dcf26387023

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Ineq
import Theorems.Thm_VariableBound_Ineq_two_le_lg
import Theorems.Thm_P2M_VariableBound_Ineq_beta_le__a4c5e212e2ce
import Theorems.Thm_P2M_VariableBound_Ineq_beta_le__a4eb7ef2dfed
import Theorems.Thm_VariableBound_Ineq_rb_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Ineq
namespace VariableBound.Ineq
theorem _root_.solution {n Δ m nb rb : ℕ} (hΔ : 2 ≤ Δ) (hnm : nb < m) (hm : m ≤ Δ * n) (h : IsNb n Δ nb) (hr : IsRb (beta n m nb) rb)
    (hn : 29 * lg (2 * Δ) + 19 ≤ n) : rb ≤ 10 * n ∧ Mb (beta n m nb) rb ≤ 14 * n := by
  have hL := two_le_lg hΔ
  have h1 := (beta_le₁ hΔ hnm hm h).trans (beta_le₂ (by omega) h)
  have h2 := rb_le hr
  have hβ : 1 ≤ beta n m nb := by unfold beta; omega
  constructor
  · have : (rb : ℝ) ≤ ((10 * n : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  · have : ((Mb (beta n m nb) rb : ℕ) : ℝ) ≤ ((14 * n : ℕ) : ℝ) := by
      unfold Mb
      rw [Nat.cast_sub (by omega)]
      push_cast
      linarith
    exact_mod_cast this
end VariableBound.Ineq
