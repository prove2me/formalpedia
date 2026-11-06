-- Prove2me | solution 1 for VariableBound.Net.SizeU.kind_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:37:58.842052+00:00
-- url     : https://prove2.me/submissions/cb35fe02-d8bc-4a65-b671-6705800f3f8b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_VariableBound_Net_Tests
import Definitions.Def_VariableBound_Params_Ineq
import Definitions.Def_ClauseBound_ParityChecks_Binom
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Net_SizeU
import Theorems.Thm_VariableBound_Net_SizeU_lg_le_lg
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_Ineq_binom
import Theorems.Thm_VariableBound_Ineq_nb_pos


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeU
open Finset Groundwork AppVariables
variable {k g n nb M : ℕ} {D : Dat} {fl : Bool} {y : ℕ}
namespace VariableBound.Net.SizeU
theorem _root_.solution (hp : ParamIneq) {k n Δ m nb M r I T μ : ℕ} (hΔ : 2 ≤ Δ) (hnm : nb < m) (hm : m ≤ Δ * n) (hnb : IsNb n Δ nb) (hk : 1 ≤ k) (hr : r ≤ M)
    (hM : 1 ≤ M) (hI : nb * I ≤ r * (16 * m)) (hT : T ≤ k * I) (hμ : μ ≤ k * M) :
    lg (T.choose μ) ≤ k * M * lg (3 * (16 * m / nb)) ∧ (k : ℝ) * M * lg (3 * (16 * m / nb)) ≤ k * M * lg (96 * Δ * lg (2 * Δ)) := by
  have hnb1 : (1 : ℝ) ≤ nb := Ineq.nb_pos hnb
  have hnb0 : (0 : ℝ) < nb := by linarith
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hs : (16 : ℝ) ≤ 16 * m / nb := by
    rw [le_div_iff₀ hnb0]
    have : (nb : ℝ) ≤ m := by exact_mod_cast hnm.le
    linarith
  refine ⟨?_, ?_⟩
  · have h1 : 1 ≤ k * M := Nat.mul_pos hk hM
    have h2 := Ineq.binom (t := T) hμ h1
    have h3 : 3 * (T : ℝ) / ((k * M : ℕ) : ℝ) ≤ 3 * (16 * m / nb) := by
      have hT' : (T : ℝ) ≤ k * I := by exact_mod_cast hT
      have hI' : (nb : ℝ) * I ≤ r * (16 * m) := by exact_mod_cast hI
      have hr' : (r : ℝ) ≤ M := by exact_mod_cast hr
      have hI2 : (I : ℝ) ≤ M * (16 * m / nb) := by
        have : (I : ℝ) ≤ r * (16 * m) / nb := by rw [le_div_iff₀ hnb0]; linarith
        refine this.trans ?_
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right hr' (by linarith)
      push_cast
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hI2 hkr.le
      nlinarith
    have h5 : lg (3 * (T : ℝ) / ((k * M : ℕ) : ℝ)) ≤ lg (3 * (16 * m / nb)) := lg_le_lg (by positivity) h3 (by linarith)
    have h6 : 1 ≤ lg (3 * (16 * (m : ℝ) / nb)) := by
      have : lg 2 = 1 := by unfold lg; exact Real.logb_self_eq_one (by norm_num)
      rw [← this]
      exact lg_le_lg (by norm_num) (by linarith) (by linarith)
    calc lg (T.choose μ) ≤ ((k * M : ℕ) : ℝ) * max 1 (lg (3 * (T : ℝ) / ((k * M : ℕ) : ℝ))) := h2
      _ ≤ ((k * M : ℕ) : ℝ) * lg (3 * (16 * m / nb)) := mul_le_mul_of_nonneg_left (max_le h6 h5) (Nat.cast_nonneg _)
      _ = k * M * lg (3 * (16 * m / nb)) := by push_cast; ring
  · have h4 := (hp.sb_lt n Δ m nb hΔ hm hnb).2
    refine mul_le_mul_of_nonneg_left (lg_le_lg (by linarith) (by linarith) (by linarith)) (by positivity)
end VariableBound.Net.SizeU
