-- Prove2me | solution 1 for ParallelLotteries.gamma_eq_f
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:04:25.371271+00:00
-- url     : https://prove2.me/submissions/58f8916e-a7e7-4fc1-a279-6a9d43d70cbd

import Mathlib
import Definitions.Def_ParallelLotteries_hf

open ParallelLotteries in
theorem solution (k : ℕ) (hk : 1 ≤ k) (pi pj yi yj : ℝ) (hpi : 0 < pi)
    (hpik : pi < 1 / (k : ℝ)) (hpjk : 1 / (k : ℝ) < pj) (hpj : pj ≤ 1) (hsum : yi + yj = 1)
    (hcost : 1 / (k : ℝ) * (yi / pi + yj / pj) = 1) :
    yi / (1 - (1 - pi) ^ k) + yj / (1 - (1 - pj) ^ k) = fval k pi pj := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hinv : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hk1
  have hpj0 : 0 < pj := lt_trans (by positivity) hpjk
  have hpipj : pi < pj := lt_trans hpik hpjk
  have hd : pj - pi ≠ 0 := sub_ne_zero.mpr (ne_of_gt hpipj)
  have hkn : k ≠ 0 := by omega
  have hAi : 1 - (1 - pi) ^ k ≠ 0 := by
    have : (1 - pi) ^ k < 1 := pow_lt_one₀ (by linarith) (by linarith) hkn
    linarith
  have hAj : 1 - (1 - pj) ^ k ≠ 0 := by
    have : (1 - pj) ^ k < 1 := pow_lt_one₀ (by linarith) (by linarith) hkn
    linarith
  have e : yi / pi + yj / pj = (k : ℝ) := by
    have h := hcost
    rw [one_div, inv_mul_eq_iff_eq_mul₀ hk0] at h
    linarith
  rw [div_add_div _ _ hpi.ne' hpj0.ne', div_eq_iff (mul_ne_zero hpi.ne' hpj0.ne')] at e
  have hyi : yi = pi * (k * pj - 1) / (pj - pi) := by
    rw [eq_div_iff hd]; linear_combination e - pi * hsum
  have hyj : yj = pj * (1 - k * pi) / (pj - pi) := by
    rw [eq_div_iff hd]; linear_combination pj * hsum - e
  unfold fval hfun
  rw [if_neg hpi.ne', if_neg hpj0.ne', hyi, hyj]
  field_simp <;> ring
