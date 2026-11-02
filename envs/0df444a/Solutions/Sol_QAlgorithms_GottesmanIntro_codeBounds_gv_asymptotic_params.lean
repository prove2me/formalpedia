-- Prove2me | solution 1 for QAlgorithms.GottesmanIntro.codeBounds_gv_asymptotic_params
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:55:40.346742+00:00
-- url     : https://prove2.me/submissions/17a11bf9-e318-4e1f-b7d3-958a9b343e9e

import Definitions.Def_QAlgorithms_Defs_FTCircuit
set_option autoImplicit false
open QAlgorithms QAlgorithms.Stabilizer
open scoped Matrix

private lemma linear_entropy_identity (q n j : ℝ) :
    j * Real.log 3 - j * Real.log q - (n - j) * Real.log (1 - q) =
      n * (q * Real.log 3 + Real.binEntropy q) +
        (j - q * n) * (Real.log 3 - Real.log q + Real.log (1 - q)) := by
  rw [Real.binEntropy, Real.log_inv, Real.log_inv]
  ring

private lemma rate_mul_log_two (q : ℝ) :
    (1 - q * Real.logb 2 3 - binEntropy2 q) * Real.log 2 =
      Real.log 2 - (q * Real.log 3 + Real.binEntropy q) := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [binEntropy2, Real.logb]
  field_simp [h2]
  ring

private lemma log_three_sub_log_add_log_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hq3 : q ≤ 3 * (1 - q)) :
    0 ≤ Real.log 3 - Real.log q + Real.log (1 - q) := by
  have h1q : 0 < 1 - q := by linarith
  have hle : Real.log q ≤ Real.log (3 * (1 - q)) := Real.log_le_log hq0 hq3
  rw [Real.log_mul (by norm_num) h1q.ne'] at hle
  linarith

private lemma q_le_three_mul_one_sub_of_pos_rate {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hrate : 0 < 1 - q * Real.logb 2 3 - binEntropy2 q) :
    q ≤ 3 * (1 - q) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hbin : 0 < Real.binEntropy q := Real.binEntropy_pos hq0 hq1
  have hmul : 0 < (1 - q * Real.logb 2 3 - binEntropy2 q) * Real.log 2 :=
    mul_pos hrate hlog2
  rw [rate_mul_log_two] at hmul
  have h16_27 : Real.log ((2 : ℝ) ^ (4 : ℕ)) < Real.log ((3 : ℝ) ^ (3 : ℕ)) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h16_27
  push_cast at h16_27
  nlinarith

private lemma term_three_pow_le {n d j : ℕ} (hjd : j ≤ d) (hdn : d ≤ n)
    {q : ℝ} (hq0 : 0 < q) (hq3 : q ≤ 3 * (1 - q)) :
    (3 : ℝ) ^ j * q ^ d * (1 - q) ^ (n - d) ≤
      (3 : ℝ) ^ d * (q ^ j * (1 - q) ^ (n - j)) := by
  have hd_eq : d = j + (d - j) := (Nat.add_sub_of_le hjd).symm
  have hn_eq : n - j = (n - d) + (d - j) := by omega
  have hpow : q ^ (d - j) ≤ (3 * (1 - q)) ^ (d - j) :=
    pow_le_pow_left₀ hq0.le hq3 (d - j)
  rw [mul_pow] at hpow
  have h1q : 0 ≤ 1 - q := by linarith
  have hnonneg : 0 ≤ (3 : ℝ) ^ j * q ^ j * (1 - q) ^ (n - d) := by positivity
  calc (3 : ℝ) ^ j * q ^ d * (1 - q) ^ (n - d)
    _ = (3 : ℝ) ^ j * (q ^ j * q ^ (d - j)) * (1 - q) ^ (n - d) := by
        rw [← pow_add, ← hd_eq]
    _ = ((3 : ℝ) ^ j * q ^ j * (1 - q) ^ (n - d)) * q ^ (d - j) := by ring
    _ ≤ ((3 : ℝ) ^ j * q ^ j * (1 - q) ^ (n - d)) * ((3 : ℝ) ^ (d - j) * (1 - q) ^ (d - j)) :=
        mul_le_mul_of_nonneg_left hpow hnonneg
    _ = ((3 : ℝ) ^ j * (3 : ℝ) ^ (d - j)) * (q ^ j * ((1 - q) ^ (n - d) * (1 - q) ^ (d - j))) := by ring
    _ = (3 : ℝ) ^ d * (q ^ j * (1 - q) ^ (n - j)) := by
        rw [← pow_add, ← hd_eq, ← pow_add, ← hn_eq]

private lemma sum_three_pow_choose_le {n d : ℕ} (hdn : d ≤ n)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hq3 : q ≤ 3 * (1 - q)) :
    ((∑ j ∈ Finset.range d, 3 ^ j * n.choose j : ℕ) : ℝ) * (q ^ d * (1 - q) ^ (n - d)) ≤
      (3 : ℝ) ^ d := by
  have h1q : 0 < 1 - q := by linarith
  push_cast
  rw [Finset.sum_mul]
  calc ∑ j ∈ Finset.range d, (3 : ℝ) ^ j * (n.choose j : ℝ) * (q ^ d * (1 - q) ^ (n - d))
    _ = ∑ j ∈ Finset.range d, ((3 : ℝ) ^ j * q ^ d * (1 - q) ^ (n - d)) * (n.choose j : ℝ) := by
        refine Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ j ∈ Finset.range d, ((3 : ℝ) ^ d * (q ^ j * (1 - q) ^ (n - j))) * (n.choose j : ℝ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjd : j ≤ d := Nat.le_of_lt (Finset.mem_range.mp hj)
        exact mul_le_mul_of_nonneg_right (term_three_pow_le hjd hdn hq0 hq3) (Nat.cast_nonneg _)
    _ = (3 : ℝ) ^ d * ∑ j ∈ Finset.range d, q ^ j * (1 - q) ^ (n - j) * (n.choose j : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
    _ ≤ (3 : ℝ) ^ d * ∑ j ∈ Finset.range (n + 1), q ^ j * (1 - q) ^ (n - j) * (n.choose j : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun j _ _ => ?_
        positivity
    _ = (3 : ℝ) ^ d * (q + (1 - q)) ^ n := by rw [← add_pow]
    _ = (3 : ℝ) ^ d := by ring

theorem solution :
    ∀ p : ℝ, 0 < p → p < 1 / 2 → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      0 < 1 - 2 * p * Real.logb 2 3 - binEntropy2 (2 * p) →
        ∃ k d : ℕ, 1 ≤ d ∧ 2 * p * n ≤ d ∧
          (∑ j ∈ Finset.range d, 3 ^ j * n.choose j) * 2 ^ k ≤ 2 ^ n ∧
          1 - 2 * p * Real.logb 2 3 - binEntropy2 (2 * p) - ε ≤ (k : ℝ) / n := by
  intro p hp0 hp12 ε hε
  by_cases hrate : 0 < 1 - 2 * p * Real.logb 2 3 - binEntropy2 (2 * p)
  · set q := 2 * p
    have hq0 : 0 < q := by linarith
    have hq1 : q < 1 := by linarith
    have h1q : 0 < 1 - q := by linarith
    have hq3 : q ≤ 3 * (1 - q) := q_le_three_mul_one_sub_of_pos_rate hq0 hq1 hrate
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    set R := 1 - q * Real.logb 2 3 - binEntropy2 q
    set C_gv := Real.log 3 - Real.log q + Real.log (1 - q)
    have hC_gv_nonneg : 0 ≤ C_gv := log_three_sub_log_add_log_nonneg hq0 hq1 hq3
    set c_gv := ⌈C_gv / Real.log 2⌉₊
    have hc_gv : C_gv ≤ (c_gv : ℝ) * Real.log 2 :=
      (div_le_iff₀ hlog2).mp (Nat.le_ceil _)
    set N := max (max 1 (⌈1 / (1 - q)⌉₊ + 1))
      (max (⌈(c_gv : ℝ) / R⌉₊ + 1) (⌈((c_gv : ℝ) + 1) / ε⌉₊ + 1))
    refine ⟨N, fun n hn _ => ?_⟩
    have hn1 : 1 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
    have hn_1q : ⌈1 / (1 - q)⌉₊ + 1 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
    have hn_R : ⌈(c_gv : ℝ) / R⌉₊ + 1 ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
    have hn_ε : ⌈((c_gv : ℝ) + 1) / ε⌉₊ + 1 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
    have hn_pos : (0 : ℝ) < n := by positivity
    set d := ⌈q * (n : ℝ)⌉₊
    have hd_pos : 1 ≤ d := Nat.ceil_pos.mpr (by positivity)
    have hd_lb : 2 * p * (n : ℝ) ≤ (d : ℝ) := Nat.le_ceil (q * (n : ℝ))
    have hd_ub : (d : ℝ) < q * (n : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
    have hdn : d ≤ n := by
      have h1 : 1 / (1 - q) ≤ (n : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈1 / (1 - q)⌉₊ ≤ n))
      have h2 : 1 ≤ (n : ℝ) * (1 - q) := (div_le_iff₀ h1q).mp h1
      have h3 : (d : ℝ) < (n : ℝ) + 1 := by linarith
      have h4 : d < n + 1 := by exact_mod_cast h3
      omega
    set m := ⌊(n : ℝ) * R⌋₊
    have hc_le_m : c_gv ≤ m := by
      rw [Nat.le_floor_iff (by positivity)]
      have h1 : (c_gv : ℝ) / R ≤ (n : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈(c_gv : ℝ) / R⌉₊ ≤ n))
      exact (div_le_iff₀ hrate).mp h1
    set k := m - c_gv
    have hk_add : k + c_gv = m := Nat.sub_add_cancel hc_le_m
    have hk_ub : (k : ℝ) + (c_gv : ℝ) ≤ (n : ℝ) * R := by
      have : ((k + c_gv : ℕ) : ℝ) ≤ (n : ℝ) * R := by
        rw [hk_add]
        exact Nat.floor_le (by positivity)
      push_cast at this
      exact this
    have hk_lb : R - ε ≤ (k : ℝ) / (n : ℝ) := by
      have hm_gt : (n : ℝ) * R - 1 < (m : ℝ) := Nat.sub_one_lt_floor _
      have hm_eq : (m : ℝ) = (k : ℝ) + (c_gv : ℝ) := by exact_mod_cast hk_add.symm
      have h1 : ((c_gv : ℝ) + 1) / ε ≤ (n : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈((c_gv : ℝ) + 1) / ε⌉₊ ≤ n))
      have h2 : (c_gv : ℝ) + 1 ≤ (n : ℝ) * ε := by
        have := (div_le_iff₀ hε).mp h1
        linarith
      rw [le_div_iff₀ hn_pos]
      linarith
    have hsum_le := sum_three_pow_choose_le hdn hq0 hq1 hq3
    have hlin := linear_entropy_identity q (n : ℝ) (d : ℝ)
    have hrate_log := rate_mul_log_two q
    have hd_diff : ((d : ℝ) - q * (n : ℝ)) * C_gv ≤ 1 * C_gv :=
      mul_le_mul_of_nonneg_right (by linarith) hC_gv_nonneg
    have hlog_bound : Real.log ((3 : ℝ) ^ d * (2 : ℝ) ^ k) ≤
        Real.log (q ^ d * (1 - q) ^ (n - d) * (2 : ℝ) ^ n) := by
      rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity),
          Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow,
          Nat.cast_sub hdn]
      nlinarith
    have hexp_bound : (3 : ℝ) ^ d * (2 : ℝ) ^ k ≤ q ^ d * (1 - q) ^ (n - d) * (2 : ℝ) ^ n := by
      rw [← Real.exp_log (by positivity : 0 < (3 : ℝ) ^ d * (2 : ℝ) ^ k),
          ← Real.exp_log (by positivity : 0 < q ^ d * (1 - q) ^ (n - d) * (2 : ℝ) ^ n)]
      exact Real.exp_le_exp.mpr hlog_bound
    have hgv_real : ((∑ j ∈ Finset.range d, 3 ^ j * n.choose j : ℕ) : ℝ) * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ n := by
      have hpos_q : 0 < q ^ d * (1 - q) ^ (n - d) := by positivity
      have hmul : (((∑ j ∈ Finset.range d, 3 ^ j * n.choose j : ℕ) : ℝ) * (2 : ℝ) ^ k) *
          (q ^ d * (1 - q) ^ (n - d)) ≤ (2 : ℝ) ^ n * (q ^ d * (1 - q) ^ (n - d)) := by
        calc (((∑ j ∈ Finset.range d, 3 ^ j * n.choose j : ℕ) : ℝ) * (2 : ℝ) ^ k) *
              (q ^ d * (1 - q) ^ (n - d))
          _ = (((∑ j ∈ Finset.range d, 3 ^ j * n.choose j : ℕ) : ℝ) * (q ^ d * (1 - q) ^ (n - d))) *
                (2 : ℝ) ^ k := by ring
          _ ≤ (3 : ℝ) ^ d * (2 : ℝ) ^ k := mul_le_mul_of_nonneg_right hsum_le (by positivity)
          _ ≤ q ^ d * (1 - q) ^ (n - d) * (2 : ℝ) ^ n := hexp_bound
          _ = (2 : ℝ) ^ n * (q ^ d * (1 - q) ^ (n - d)) := by ring
      exact le_of_mul_le_mul_right hmul hpos_q
    have hgv_nat : (∑ j ∈ Finset.range d, 3 ^ j * n.choose j) * 2 ^ k ≤ 2 ^ n := by
      exact_mod_cast hgv_real
    exact ⟨k, d, hd_pos, hd_lb, hgv_nat, hk_lb⟩
  · exact ⟨0, fun _ _ h => False.elim (hrate h)⟩
