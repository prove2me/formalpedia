-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.hermite_discretization_budget
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-24T23:23:27.669822+00:00
-- url     : https://prove2.me/submissions/e183f35a-5442-455d-b174-72ac6d14b811

import Mathlib

set_option autoImplicit false

theorem solution (n D M η : ℝ)
    (hn : 0 ≤ n) (hD : 0 ≤ D+1) (hM : 0 < M) (hη : 0 < η)
    (h1 : 20736*n^2*(D+1)/η^2 ≤ M)
    (h2 : 165888*n/η^4 ≤ M)
    (h3 : 4/Real.pi * Real.log (12*Real.sqrt (2*n)/η) ≤ M) :
    24*n*Real.sqrt ((D+1)/M) + 2*(8*n/M)^(1/4:ℝ) +
      2*Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) ≤ η/2 := by
  have hterm1 : 24*n*Real.sqrt ((D+1)/M) ≤ η/6 := by
    have hh := (div_le_iff₀ (sq_pos_of_pos hη)).mp h1
    have hs := Real.sq_sqrt (div_nonneg hD hM.le)
    have hm := (div_mul_cancel₀ (D+1) hM.ne')
    have hsq : (24*n*Real.sqrt ((D+1)/M))^2 ≤ (η/6)^2 := by
      apply (mul_le_mul_iff_left₀ hM).mp
      calc
        _ = 576*n^2*(D+1) := by rw [mul_pow,mul_pow,hs]; field_simp; ring
        _ ≤ (η/6)^2*M := by nlinarith
    have hp : 0 ≤ 24*n*Real.sqrt ((D+1)/M) := by positivity
    nlinarith
  have hterm2 : 2*(8*n/M)^(1/4:ℝ) ≤ η/6 := by
    have hh := (div_le_iff₀ (pow_pos hη 4)).mp h2
    have hratio : 8*n/M ≤ (η/12)^4 := by
      apply (div_le_iff₀ hM).mpr
      nlinarith
    have hroot := Real.rpow_le_rpow (by positivity : 0 ≤ 8*n/M) hratio
      (by norm_num : (0:ℝ) ≤ 1/4)
    have hpow : ((η/12)^4)^(1/4:ℝ) = η/12 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ η/12)]
      norm_num
    rw [hpow] at hroot
    linarith
  have hterm3 : 2*Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) ≤ η/6 := by
    by_cases hn0 : n = 0
    · subst n; simp; positivity
    · have hnpos : 0 < n := lt_of_le_of_ne hn (Ne.symm hn0)
      have harg : 0 < 12*Real.sqrt (2*n)/η := by positivity
      have hlog : Real.log (12*Real.sqrt (2*n)/η) ≤ Real.pi*M/4 := by
        have hh := mul_le_mul_of_nonneg_left h3 (Real.pi_pos.le)
        field_simp at hh
        nlinarith
      have hexp : Real.exp (-Real.pi*M/4) ≤
          Real.exp (-Real.log (12*Real.sqrt (2*n)/η)) :=
        Real.exp_le_exp.mpr (by linarith)
      rw [Real.exp_neg,Real.exp_log harg] at hexp
      have hmult := mul_le_mul_of_nonneg_left hexp
        (by positivity : 0 ≤ 2*Real.sqrt (2*n))
      calc
        _ ≤ 2*Real.sqrt (2*n)*(12*Real.sqrt (2*n)/η)⁻¹ := hmult
        _ = η/6 := by field_simp; norm_num
  linarith
