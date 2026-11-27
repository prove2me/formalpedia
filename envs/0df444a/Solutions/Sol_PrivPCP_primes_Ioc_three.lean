-- Prove2me | solution 1 for PrivPCP.primes_Ioc_three
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T03:14:53.465154+00:00
-- url     : https://prove2.me/submissions/e923b405-5b26-485d-90bc-b772e6e86e04

import Mathlib


namespace PrivPCP.P3

open Real Chebyshev

lemma theta_nat (n : ℕ) : θ (n : ℝ) = ∑ i ∈ Finset.Ioc 0 n, if i.Prime then Real.log i else 0 := by
  rw [theta, Nat.floor_natCast, Finset.sum_filter]

lemma theta_diff (m : ℕ) :
    θ ((3 * m : ℕ) : ℝ) - θ (m : ℝ) = ∑ p ∈ (Finset.Ioc m (3 * m)).filter Nat.Prime, Real.log p := by
  rw [theta_nat, theta_nat, Finset.sum_filter, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le m)
    (by omega : m ≤ 3 * m)]
  ring

lemma count_bound (m : ℕ) (hm : 1 ≤ m) :
    θ ((3 * m : ℕ) : ℝ) - θ (m : ℝ) ≤
      ((Finset.Ioc m (3 * m)).filter Nat.Prime).card * Real.log (3 * m) := by
  rw [theta_diff]
  have := Finset.sum_le_card_nsmul ((Finset.Ioc m (3 * m)).filter Nat.Prime) (fun p => Real.log p)
    (Real.log (3 * m)) (by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
      apply Real.log_le_log
      · have : (0 : ℝ) < p := by exact_mod_cast hp.2.pos
        exact this
      · have : (p : ℝ) ≤ ((3 * m : ℕ) : ℝ) := by exact_mod_cast hp.1.2
        push_cast at this; exact this)
  simpa [nsmul_eq_mul] using this

/-- the Chebyshev lower bound for primes in `(m, 3m]`, before choosing constants -/
lemma count_lower (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) * Real.log 2 - Real.log (3 * m + 1) - 2 * √(3 * m) * Real.log (3 * m) ≤
      ((Finset.Ioc m (3 * m)).filter Nat.Prime).card * Real.log (3 * m) := by
  have h1 := theta_ge (3 * m)
  have h2 := theta_le_log4_mul_x (x := (m : ℝ)) (by positivity)
  have h3 := count_bound m hm
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  push_cast at h1 h3
  rw [h4] at h2
  linarith

end PrivPCP.P3


namespace PrivPCP.P3

open Real

lemma log_two_bounds : (0.69 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.7 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  constructor <;> linarith

/-- the error terms are small -/
lemma err_small (M : ℝ) (hM : 2 * 10 ^ 8 ≤ M) :
    Real.log (3 * M + 1) + 2 * √(3 * M) * Real.log (3 * M) ≤ M * Real.log 2 / 2 := by
  obtain ⟨hl2, hl2'⟩ := log_two_bounds
  have hM0 : 0 < M := by linarith
  set w := √(√(3 * M)) with hw
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw2 : w ^ 2 = √(3 * M) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hw4 : w ^ 4 = 3 * M := by
    rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, hw2, Real.sq_sqrt (by linarith)]
  have hw100 : 100 ≤ w := by
    by_contra h
    push Not at h
    have : w ^ 4 < 100 ^ 4 := pow_lt_pow_left₀ h hw0 (by norm_num)
    rw [hw4] at this
    norm_num at this
    linarith
  have hwpos : 0 < w := by linarith
  have hlog3M : Real.log (3 * M) = 4 * Real.log w := by
    rw [← hw4, Real.log_pow]; norm_num
  have hlogw : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos hwpos
  have hL : Real.log (3 * M) ≤ 4 * w := by rw [hlog3M]; linarith
  have hL1 : Real.log (3 * M + 1) ≤ Real.log 2 + Real.log (3 * M) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hsq : √(3 * M) = w ^ 2 := hw2.symm
  have hT : 2 * √(3 * M) * Real.log (3 * M) ≤ 8 * w ^ 3 := by
    rw [hsq]
    have := mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 2 * w ^ 2)
    nlinarith
  have hMw : M = w ^ 4 / 3 := by rw [hw4]; ring
  have hw3 : 100 * w ^ 3 ≤ w ^ 4 := by
    have := mul_le_mul_of_nonneg_right hw100 (by positivity : (0 : ℝ) ≤ w ^ 3)
    nlinarith
  have hw1 : 10000 * w ≤ w ^ 3 := by
    have h1 : 100 * w ≤ w ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hw0
    nlinarith
  have key : 0.7 + 4 * w + 8 * w ^ 3 ≤ M * 0.69 / 2 := by
    rw [hMw]
    nlinarith
  have : M * 0.69 / 2 ≤ M * Real.log 2 / 2 := by nlinarith
  linarith

/-- `t log (3M)` is small compared to `M` -/
lemma t_small (t : ℕ) (ht : 1 ≤ t) (M : ℝ) (hM : (10 : ℝ) ^ 8 * t * Real.log (t + 1) ≤ M) :
    (t : ℝ) * Real.log (3 * M) ≤ M * Real.log 2 / 2 := by
  obtain ⟨hl2, hl2'⟩ := log_two_bounds
  have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
  set ℓ := Real.log (t + 1) with hℓ
  have hℓ2 : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by linarith)
  have hℓ0 : 0 < ℓ := by linarith
  set m0 : ℝ := 10 ^ 8 * t * ℓ with hm0
  have hm0pos : 0 < m0 := by positivity
  have hM0 : 0 < M := by linarith
  -- `log (3M) = log (3 m0) + log (M / m0)`
  have hsplit : Real.log (3 * M) = Real.log (3 * m0) + Real.log (M / m0) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1; field_simp
  have hlr : Real.log (M / m0) ≤ M / m0 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  -- `log (3 m0) ≤ 37 ℓ`
  have h3 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have h10 : Real.log ((10 : ℝ) ^ 8) ≤ 32 * Real.log 2 := by
    rw [Real.log_pow, show (32 : ℝ) * Real.log 2 = ((8 : ℕ) : ℝ) * (4 * Real.log 2) by push_cast; ring]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hlt : Real.log t ≤ ℓ := Real.log_le_log (by linarith) (by linarith)
  have hll : Real.log ℓ ≤ ℓ - 1 := Real.log_le_sub_one_of_pos hℓ0
  have hlm0 : Real.log (3 * m0) = Real.log 3 + Real.log ((10 : ℝ) ^ 8) + Real.log t + Real.log ℓ := by
    rw [hm0, show (3 : ℝ) * (10 ^ 8 * t * ℓ) = ((3 * 10 ^ 8) * t) * ℓ by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity)]
  have hb : Real.log (3 * m0) ≤ 37 * ℓ := by
    rw [hlm0]; nlinarith
  -- assemble
  have e1 : (t : ℝ) * Real.log (3 * M) ≤ t * Real.log (3 * m0) + t * (M / m0) := by
    rw [hsplit]
    have := mul_le_mul_of_nonneg_left hlr (by positivity : (0 : ℝ) ≤ t)
    nlinarith
  have e2 : (t : ℝ) * Real.log (3 * m0) ≤ 37 * (m0 / 10 ^ 8) := by
    have h1 := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ t)
    have h2 : m0 / 10 ^ 8 = t * ℓ := by rw [hm0]; field_simp
    rw [h2]
    linarith
  have e3 : (t : ℝ) * (M / m0) = M / (10 ^ 8 * ℓ) := by
    rw [hm0]; field_simp
  have e4 : M / (10 ^ 8 * ℓ) ≤ M / (10 ^ 8 * 0.69) := by
    apply div_le_div_of_nonneg_left hM0.le (by norm_num)
    nlinarith
  have e5 : 37 * (m0 / 10 ^ 8) ≤ 37 * (M / 10 ^ 8) := by
    have : m0 / 10 ^ 8 ≤ M / 10 ^ 8 := div_le_div_of_nonneg_right hM (by norm_num)
    linarith
  have e6 : 37 * (M / 10 ^ 8) + M / (10 ^ 8 * 0.69) ≤ M * 0.69 / 2 := by
    have hc : (37 / 10 ^ 8 + 1 / (10 ^ 8 * 0.69) : ℝ) ≤ 0.345 := by norm_num
    calc 37 * (M / 10 ^ 8) + M / (10 ^ 8 * 0.69) = M * (37 / 10 ^ 8 + 1 / (10 ^ 8 * 0.69)) := by ring
      _ ≤ M * 0.345 := mul_le_mul_of_nonneg_left hc hM0.le
      _ = M * 0.69 / 2 := by ring
  have : M * 0.69 / 2 ≤ M * Real.log 2 / 2 := by nlinarith
  linarith

end PrivPCP.P3

open PrivPCP.P3 in
theorem solution : ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ t : ℕ, 1 ≤ t → ∀ m : ℕ,
    A₀ * t * Real.log (t + 1) ≤ m → t ≤ ((Finset.Ioc m (3 * m)).filter Nat.Prime).card := by
  refine ⟨10 ^ 9, by norm_num, fun t ht m hm => ?_⟩
  obtain ⟨hl2, hl2'⟩ := log_two_bounds
  have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hℓ : Real.log 2 ≤ Real.log ((t : ℝ) + 1) := Real.log_le_log (by norm_num) (by linarith)
  have htl : (0.69 : ℝ) ≤ t * Real.log ((t : ℝ) + 1) := by nlinarith
  have hM' : (2 : ℝ) * 10 ^ 8 ≤ m := by nlinarith
  have hm8 : (10 : ℝ) ^ 8 * t * Real.log (t + 1) ≤ m := by
    have : (0 : ℝ) ≤ t * Real.log ((t : ℝ) + 1) := by linarith
    nlinarith
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hc := count_lower m hm1
  have he := err_small (m : ℝ) hM'
  have hts := t_small t ht (m : ℝ) hm8
  have hlog : 0 < Real.log (3 * (m : ℝ)) := Real.log_pos (by linarith)
  have : (t : ℝ) * Real.log (3 * m) ≤
      ((Finset.Ioc m (3 * m)).filter Nat.Prime).card * Real.log (3 * m) := by linarith
  have := le_of_mul_le_mul_right this hlog
  exact_mod_cast this


