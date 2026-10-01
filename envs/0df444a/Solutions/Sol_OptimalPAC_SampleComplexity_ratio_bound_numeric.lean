-- Prove2me | solution 1 for OptimalPAC.SampleComplexity.ratio_bound_numeric
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T08:23:39.874285+00:00
-- url     : https://prove2.me/submissions/017843d8-4066-4c54-b8b6-36398d43feda

import Mathlib
import Definitions.Def_OptimalPAC_SampleComplexity_Model

set_option autoImplicit false

/-- `log (max (K N) 2) / N ≤ max (log (K N₀)) 1 / N₀` for `N ≥ N₀ > 0`. -/
lemma rbn70_key (K N N0 : ℝ) (hK : 0 < K) (hN0 : 0 < N0) (hN : N0 ≤ N) :
    Real.log (max (K * N) 2) * N0 ≤ max (Real.log (K * N0)) 1 * N := by
  have hNpos : 0 < N := lt_of_lt_of_le hN0 hN
  have hM1 : 1 ≤ max (Real.log (K * N0)) 1 := le_max_right _ _
  have hMl : Real.log (K * N0) ≤ max (Real.log (K * N0)) 1 := le_max_left _ _
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hratio : 1 ≤ N / N0 := by rw [le_div_iff₀ hN0]; linarith
  have hbound : Real.log (max (K * N) 2) ≤ max (Real.log (K * N0)) 1 + N / N0 - 1 := by
    rcases le_total (K * N) 2 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]
      have hKN0 : 0 < K * N0 := mul_pos hK hN0
      have e1 : K * N = (K * N0) * (N / N0) := by field_simp
      rw [e1, Real.log_mul hKN0.ne' (by positivity)]
      have := Real.log_le_sub_one_of_pos (show 0 < N / N0 by positivity)
      linarith
  have h1 := mul_le_mul_of_nonneg_right hbound hN0.le
  have h2 : N / N0 * N0 = N := div_mul_cancel₀ N hN0.ne'
  have h3 := mul_le_mul_of_nonneg_left hN (show 0 ≤ max (Real.log (K * N0)) 1 - 1 by linarith)
  have h4 : (max (Real.log (K * N0)) 1 + N / N0 - 1) * N0
      = (max (Real.log (K * N0)) 1 - 1) * N0 + N := by
    linear_combination h2
  linarith

lemma rbn70_final (l2 d u L9 q m : ℝ) (hl2 : 69 / 100 < l2) (hd : 1 ≤ d) (hu : 4 * l2 ≤ u)
    (hL9 : L9 ≤ 4 * l2) (hm : 1800 ≤ m) (hq : m - 3 ≤ 4 * q) :
    20 / 7 * (13 * l2 * d + (L9 + u) + u) * (m + 1) < 150 * (d + u) * l2 * q := by
  have hl2p : 0 < l2 := by linarith
  have hup : 0 < u := by linarith
  have a1 := mul_le_mul_of_nonneg_left hq (show 0 ≤ 525 / 2 * (d + u) * l2 by positivity)
  have a2 : 0 ≤ l2 * d * (5 / 2 * m - 2095 / 2) :=
    mul_nonneg (by positivity) (by linarith)
  have a3' := mul_le_mul_of_nonneg_right hl2.le (show 0 ≤ m - 3 by linarith)
  have a3 : 0 < 525 / 2 * l2 * (m - 3) - 60 * (m + 1) := by nlinarith
  have a3'' : 0 ≤ 525 / 2 * l2 * (m - 3) - 40 * (m + 1) := by linarith
  have a4 : 0 ≤ (u - 4 * l2) * (525 / 2 * l2 * (m - 3) - 40 * (m + 1)) :=
    mul_nonneg (by linarith) a3''
  have a5 := mul_le_mul_of_nonneg_right hL9 (show 0 ≤ m + 1 by linarith)
  have a6 : 0 < l2 * (525 / 2 * l2 * (m - 3) - 60 * (m + 1)) := mul_pos hl2p a3
  nlinarith

lemma rbn70_b (L u d q m : ℝ) (hL : L ≤ u) (hu : 0 < u) (hd : 1 ≤ d) (hm : 1800 ≤ m)
    (hq : m - 3 ≤ 4 * q) :
    23 * L * (m + 1) < 150 * (d + u) * q := by
  have b1 := mul_le_mul_of_nonneg_left hq (show 0 ≤ 75 / 2 * (d + u) by positivity)
  have b2 := mul_le_mul_of_nonneg_right hL (show 0 ≤ m + 1 by linarith)
  have b3 : 0 < d * (m - 3) := mul_pos (by linarith) (by linarith)
  have b4 : 0 ≤ u * (29 / 2 * m - 271 / 2) := mul_nonneg hu.le (by linarith)
  nlinarith

set_option maxHeartbeats 1000000 in
open OptimalPAC.SampleComplexity in
theorem solution (m d : ℕ) (hm : 1800 * Real.log (18 * Real.exp 1) - 1 < m)
    (hd : 1 ≤ d) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∀ (p : ℝ) (N : ℕ),
      23 / ((m / 4 : ℕ) : ℝ) * Real.log (9 / δ) ≤ p →
      p ≤ 4 * 1800 / (m : ℝ) * (d + Real.log (9 * 18 / δ)) →
      7 / 10 * p * ((m / 4 : ℕ) : ℝ) ≤ N →
      p * (2 / (N : ℝ) * ((d : ℝ) * Log2 (2 * Real.exp 1 * N / d) + Log2 (18 / δ))) <
        150 / ((m : ℝ) + 1) * (d + Real.log (18 / δ))) ∧
    23 / ((m / 4 : ℕ) : ℝ) * Real.log (9 / δ) <
      150 / ((m : ℝ) + 1) * (d + Real.log (18 / δ)) := by
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hl2p : 0 < Real.log 2 := by linarith
  -- m ≥ 1800
  have hm1800 : (1800 : ℝ) ≤ m := by
    have h1 : 1 ≤ Real.log (18 * Real.exp 1) := by
      rw [Real.log_mul (by norm_num) (Real.exp_pos 1).ne', Real.log_exp]
      have : 0 < Real.log 18 := Real.log_pos (by norm_num)
      linarith
    have h2 : (1799 : ℝ) < m := by linarith
    have h3 : (1799 : ℕ) < m := by exact_mod_cast h2
    exact_mod_cast (show 1800 ≤ m by omega)
  have hmpos : (0 : ℝ) < m := by linarith
  -- q
  have hq4 : (m : ℝ) - 3 ≤ 4 * ((m / 4 : ℕ) : ℝ) := by
    have h : m ≤ 4 * (m / 4) + 3 := by omega
    have h' : (m : ℝ) ≤ 4 * ((m / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast h
    linarith
  have hq4' : 4 * ((m / 4 : ℕ) : ℝ) ≤ m := by
    have h : 4 * (m / 4) ≤ m := by omega
    exact_mod_cast h
  set q : ℝ := ((m / 4 : ℕ) : ℝ) with hqdef
  have hqpos : 0 < q := by linarith
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  -- logs
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hu4 : 4 * Real.log 2 ≤ Real.log (18 / δ) := by
    rw [← hlog16]
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hδ0]; linarith
  have hL9 : Real.log 9 ≤ 4 * Real.log 2 := by
    rw [← hlog16]; exact Real.log_le_log (by norm_num) (by norm_num)
  have hL9pos : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hw : Real.log (9 * 18 / δ) = Real.log 9 + Real.log (18 / δ) := by
    rw [show (9 : ℝ) * 18 / δ = 9 * (18 / δ) by ring]
    exact Real.log_mul (by norm_num) (by positivity)
  have h9le : Real.log (9 / δ) ≤ Real.log (18 / δ) := by
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_right (by norm_num) hδ0.le
  have h9pos : 0 < Real.log (9 / δ) := by
    apply Real.log_pos
    rw [one_lt_div hδ0]; linarith
  set u := Real.log (18 / δ) with hudef
  have hup : 0 < u := by linarith
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  refine ⟨?_, ?_⟩
  · intro p N hp1 hp2 hN
    rw [hw] at hp2
    set w := Real.log 9 + u with hwdef
    have hwpos : 0 < w := by linarith
    have hp : 0 < p := lt_of_lt_of_le (by positivity) hp1
    set N0 := 7 / 10 * p * q with hN0def
    have hN0 : 0 < N0 := by positivity
    have hNpos : (0 : ℝ) < N := lt_of_lt_of_le hN0 hN
    -- p q ≤ 1800 (d + w)
    have hpm : p * m ≤ 7200 * (d + w) := by
      have e : 4 * 1800 / (m : ℝ) * (d + w) * m = 7200 * (d + w) := by
        field_simp; ring
      have := mul_le_mul_of_nonneg_right hp2 hmpos.le
      linarith
    have hpq : p * q ≤ 1800 * (d + w) := by
      have := mul_le_mul_of_nonneg_left hq4' hp.le
      nlinarith
    -- K
    set K := 2 * Real.exp 1 / d with hKdef
    have hK : 0 < K := by positivity
    have hkey := rbn70_key K N N0 hK hN0 hN
    set M := max (Real.log (K * N0)) 1 with hMdef
    -- bound M
    have hKN0 : K * N0 ≤ 2520 * Real.exp 1 * ((d + w) / d) := by
      rw [hKdef, hN0def]
      have he : 0 < Real.exp 1 := Real.exp_pos 1
      rw [div_mul_eq_mul_div, div_le_iff₀ hdpos]
      have : 2520 * Real.exp 1 * ((d + w) / d) * d = 2520 * Real.exp 1 * (d + w) := by
        field_simp
      rw [this]
      nlinarith
    have hlog2520 : Real.log (2520 * Real.exp 1) ≤ 13 * Real.log 2 := by
      have : Real.log ((2 : ℝ) ^ 13) = 13 * Real.log 2 := by
        rw [Real.log_pow]; norm_num
      rw [← this]
      apply Real.log_le_log (by positivity)
      have := Real.exp_one_lt_d9
      norm_num; linarith
    have hMb : M ≤ 13 * Real.log 2 + w / d := by
      have hwd : 0 ≤ w / d := by positivity
      apply max_le
      · have hpos : 0 < K * N0 := mul_pos hK hN0
        have h1 := Real.log_le_log hpos hKN0
        have h1' : Real.log (2520 * Real.exp 1 * ((d + w) / d))
            = Real.log (2520 * Real.exp 1) + Real.log ((d + w) / d) :=
          Real.log_mul (by positivity) (by positivity)
        have h2 := Real.log_le_sub_one_of_pos (show 0 < (d + w) / d by positivity)
        have h3 : (d + w) / d - 1 = w / d := by field_simp; ring
        linarith
      · linarith
    have hdM : d * M ≤ 13 * Real.log 2 * d + w := by
      have := mul_le_mul_of_nonneg_left hMb hdpos.le
      have e : d * (w / d) = w := by field_simp
      nlinarith
    -- the main quantity
    set A := Real.log (max (K * N) 2) with hAdef
    have hS : p * q * (d * A + u) ≤ 10 / 7 * (13 * Real.log 2 * d + w + u) * N := by
      have s1 := mul_le_mul_of_nonneg_left hkey hdpos.le
      have s2 := mul_le_mul_of_nonneg_right hdM hNpos.le
      have s3 := mul_le_mul_of_nonneg_left hN hup.le
      rw [hN0def] at s1 s3
      linarith
    have hF := rbn70_final (Real.log 2) d u (Real.log 9) q m (by linarith) hd' hu4 hL9 hm1800
      hq4
    -- rewrite the goal
    have h18 : max (18 / δ) 2 = 18 / δ := by
      apply max_eq_left
      rw [le_div_iff₀ hδ0]; linarith
    have hKN : 2 * Real.exp 1 * (N : ℝ) / d = K * N := by rw [hKdef]; ring
    have hgoal : p * (2 / (N : ℝ) * ((d : ℝ) * Log2 (2 * Real.exp 1 * N / d) + Log2 (18 / δ)))
        = 2 * p * (d * A + u) / (N * Real.log 2) := by
      simp only [Log2, Real.logb]
      rw [hKN, h18]
      field_simp
      rw [hAdef, hudef, mul_comm (N : ℝ) K]
    rw [hgoal, div_lt_iff₀ (by positivity)]
    have t1 := mul_le_mul_of_nonneg_left hS (show (0 : ℝ) ≤ 2 * (m + 1) by positivity)
    have t2 := mul_lt_mul_of_pos_left hF hNpos
    have t3 : q * (2 * p * (d * A + u)) < q * (150 / ((m : ℝ) + 1) * (d + u) * (N * Real.log 2)) := by
      have e : 150 / ((m : ℝ) + 1) * (d + u) * (N * Real.log 2) * (m + 1)
          = 150 * (d + u) * Real.log 2 * N := by field_simp
      have t4 : q * (2 * p * (d * A + u)) * (m + 1) <
          q * (150 / ((m : ℝ) + 1) * (d + u) * (N * Real.log 2)) * (m + 1) := by
        have e2 : q * (150 / ((m : ℝ) + 1) * (d + u) * (N * Real.log 2)) * (m + 1)
            = q * (150 * (d + u) * Real.log 2 * N) := by rw [mul_assoc, e]
        rw [e2]
        linarith
      exact lt_of_mul_lt_mul_right t4 hm1.le
    exact lt_of_mul_lt_mul_left t3 hqpos.le
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_div_iff₀ hqpos hm1]
    exact rbn70_b (Real.log (9 / δ)) u d q m h9le hup hd' hm1800 hq4
