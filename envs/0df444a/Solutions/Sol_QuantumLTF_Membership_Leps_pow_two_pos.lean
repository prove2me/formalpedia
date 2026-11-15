-- Prove2me | solution 1 for QuantumLTF.Membership.Leps_pow_two_pos
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T04:25:17.604249+00:00
-- url     : https://prove2.me/submissions/0b8930e6-db3a-4265-9c3f-e4394ac06c11

import Mathlib
import Definitions.Def_QuantumLTF_Membership_Leps
import Definitions.Def_QuantumLTF_Membership_Teps

open QuantumLTF.Membership

theorem solution (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ m : ℕ, 1 ≤ m ∧ Leps ε = (2 : ℝ) ^ m := by
  let m := ⌈Real.logb 2 (20 * Teps ε)⌉₊
  refine ⟨m, ?_, rfl⟩
  have hinv : (2 : ℝ) ≤ 1 / ε := by
    apply (le_div_iff₀ hε).2
    nlinarith
  have hinvpos : 0 < (1 / ε : ℝ) := by positivity
  have hlogle : Real.log 2 ≤ Real.log (1 / ε) := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) hinvpos hinv
  have hlog2half : (1 / 2 : ℝ) < Real.log 2 := by
    exact lt_trans (by norm_num : (1 / 2 : ℝ) < 0.6931471803) Real.log_two_gt_d9
  have hinside : 1 < 2 * Real.log (1 / ε) := by nlinarith
  have hinside' : 1 < -(2 * Real.log ε) := by
    rw [Real.log_div one_ne_zero (ne_of_gt hε)] at hinside
    norm_num at hinside
    nlinarith
  have hT : 1 < Teps ε := by
    unfold Teps
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
    exact hinside'
  have harg : 1 < 20 * Teps ε := by nlinarith
  have hlogb : 0 < Real.logb 2 (20 * Teps ε) :=
    Real.logb_pos (by norm_num) harg
  exact Nat.ceil_pos.mpr hlogb
