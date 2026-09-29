-- Prove2me | solution 1 for SchrodingerEquation.quantized_wavenumber
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T08:55:01.590849+00:00
-- url     : https://prove2.me/submissions/ac5450b3-b509-41f0-b5e9-49f0f4d61a17

import Definitions.Def_SchrodingerEquation_infinite_well_model

open SchrodingerEquation

theorem solution (k L : ℝ) (hk : 0 < k) (hL : 0 < L)
    (h : Real.sin (k * L) = 0) :
    ∃ n : ℕ, 1 ≤ n ∧ k * L = (n : ℝ) * Real.pi := by
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 h
  have hpos : 0 < (n : ℝ) * Real.pi := by rw [hn]; positivity
  have hn0 : 0 < n := by
    by_contra hc
    push Not at hc
    have : (n : ℝ) ≤ 0 := by exact_mod_cast hc
    nlinarith [Real.pi_pos]
  refine ⟨n.toNat, by omega, ?_⟩
  rw [← hn]
  congr 1
  have : ((n.toNat : ℤ) : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn0.le
  rw [← this]; norm_cast
