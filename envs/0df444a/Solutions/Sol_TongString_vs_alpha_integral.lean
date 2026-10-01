-- Prove2me | solution 1 for TongString.vs_alpha_integral
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T09:51:30.662499+00:00
-- url     : https://prove2.me/submissions/534a186b-192f-4f9e-906a-87bb5f1aa388

import Mathlib

open Complex MeasureTheory in
theorem solution (a b : ℂ) (hab : (a + b).re < 1) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ α in Set.Ioi (0 : ℝ),
        (α : ℂ) ^ (-a - b) * Complex.exp (-((β * (1 - β) : ℝ) : ℂ) * α)) =
      ((β * (1 - β) : ℝ) : ℂ) ^ (a + b - 1) * Gamma (1 - a - b) := by
  obtain ⟨h0, h1⟩ := hβ
  have hc : 0 < β * (1 - β) := mul_pos h0 (by linarith)
  have hre : 0 < (1 - a - b).re := by
    simp only [Complex.sub_re, Complex.one_re]
    simp only [Complex.add_re] at hab
    linarith
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hre hc
  have e1 : (1 - a - b - 1 : ℂ) = -a - b := by ring
  rw [e1] at h
  simp only [neg_mul] at h ⊢
  rw [h]
  congr 1
  have harg : (((β * (1 - β) : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hc.le]
    exact Real.pi_pos.ne
  rw [one_div, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
  congr 1
  ring
