-- Prove2me | solution 1 for P2M_VariableBound_Ineq_beta_le__a4c5e212e2ce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:57:18.920874+00:00
-- url     : https://prove2.me/submissions/2a6cd7ab-6218-4cef-83c4-148b26966a66

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
import Theorems.Thm_VariableBound_Ineq_binom
import Theorems.Thm_VariableBound_Ineq_three_m_lt
import Theorems.Thm_VariableBound_Ineq_six_le
import Theorems.Thm_ClauseBound_ParityChecks_Binom_clog_le_logb_add_one
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Ineq
namespace VariableBound.Ineq
theorem _root_.solution {n Δ m nb : ℕ} (hΔ : 2 ≤ Δ) (hnm : nb < m) (hm : m ≤ Δ * n) (h : IsNb n Δ nb) :
    (beta n m nb : ℝ) ≤ n + 3 * (nb + 1) * lg (2 * Δ) + 2 := by
  have hL := two_le_lg hΔ
  have hc := ClauseBound.ParityChecks.Binom.clog_le_logb_add_one (x := m.choose (nb + 1)) (Nat.choose_pos hnm)
  have hb : Real.logb 2 (m.choose (nb + 1)) ≤ ((nb + 1 : ℕ) : ℝ) * max 1 (Real.logb 2 (3 * m / ((nb + 1 : ℕ) : ℝ))) :=
    binom (t := m) (μ := nb + 1) (μ' := nb + 1) le_rfl (Nat.le_add_left 1 nb)
  have h0 : (0 : ℝ) < 3 * m / (nb + 1) := by
    have : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    positivity
  have h3 : Real.logb 2 (3 * m / (nb + 1)) ≤ 3 * lg (2 * Δ) := by
    have h4 := Real.logb_le_logb_of_le (b := 2) (by norm_num) h0 ((three_m_lt hΔ hm h).le.trans (six_le hΔ))
    rwa [Real.logb_pow, Nat.cast_ofNat] at h4
  have h5 : max 1 (Real.logb 2 (3 * m / (nb + 1))) ≤ 3 * lg (2 * Δ) := max_le (by linarith) h3
  have h6 : ((nb + 1 : ℕ) : ℝ) * max 1 (Real.logb 2 (3 * m / ((nb + 1 : ℕ) : ℝ))) ≤ (nb + 1) * (3 * lg (2 * Δ)) := by
    push_cast
    exact mul_le_mul_of_nonneg_left h5 (by positivity)
  unfold beta
  push_cast
  linarith
end VariableBound.Ineq
