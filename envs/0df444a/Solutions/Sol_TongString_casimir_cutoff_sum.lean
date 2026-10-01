-- Prove2me | solution 1 for TongString.casimir_cutoff_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T17:13:00.629983+00:00
-- url     : https://prove2.me/submissions/3dbedd93-1a76-425d-a490-10282705173d

import Mathlib

set_option maxHeartbeats 1000000 in
theorem dc97380a_Q_bound (ε t : ℝ) (h0 : 0 < ε) (h1 : ε < 1) (ht : |t| ≤ 1 / 100) :
    |(-12 * ε ^ 4 * t ^ 2 - 24 * t + ε ^ 6 * t ^ 2 - 2 * ε ^ 2 * t + ε ^ 4 * t / 3 + 1 / 4
      + ε ^ 5 * t / 12 + ε / 12 + 7 * ε ^ 2 / 144 + ε ^ 3 / 72 + ε ^ 4 / 576)| ≤ 1 := by
  have e2 : 0 ≤ ε ^ 2 := by positivity
  have e2' : ε ^ 2 ≤ 1 := pow_le_one₀ h0.le h1.le
  have e3 : 0 ≤ ε ^ 3 := by positivity
  have e3' : ε ^ 3 ≤ 1 := pow_le_one₀ h0.le h1.le
  have e4 : 0 ≤ ε ^ 4 := by positivity
  have e4' : ε ^ 4 ≤ 1 := pow_le_one₀ h0.le h1.le
  have e5 : 0 ≤ ε ^ 5 := by positivity
  have e5' : ε ^ 5 ≤ 1 := pow_le_one₀ h0.le h1.le
  have e6 : 0 ≤ ε ^ 6 := by positivity
  have e6' : ε ^ 6 ≤ 1 := pow_le_one₀ h0.le h1.le
  obtain ⟨tl, tu⟩ := abs_le.mp ht
  have t2 : t ^ 2 ≤ 1 / 10000 := by nlinarith
  have t2' : 0 ≤ t ^ 2 := sq_nonneg t
  have a1 : |ε ^ 4 * t ^ 2| ≤ 1 / 10000 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith
  have a2 : |ε ^ 6 * t ^ 2| ≤ 1 / 10000 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith
  have a3 : |ε ^ 2 * t| ≤ 1 / 100 := by
    rw [abs_mul, abs_of_nonneg e2]; nlinarith [abs_nonneg t]
  have a4 : |ε ^ 4 * t| ≤ 1 / 100 := by
    rw [abs_mul, abs_of_nonneg e4]; nlinarith [abs_nonneg t]
  have a5 : |ε ^ 5 * t| ≤ 1 / 100 := by
    rw [abs_mul, abs_of_nonneg e5]; nlinarith [abs_nonneg t]
  obtain ⟨b1, c1⟩ := abs_le.mp a1
  obtain ⟨b2, c2⟩ := abs_le.mp a2
  obtain ⟨b3, c3⟩ := abs_le.mp a3
  obtain ⟨b4, c4⟩ := abs_le.mp a4
  obtain ⟨b5, c5⟩ := abs_le.mp a5
  rw [abs_le]
  constructor <;> nlinarith

open Filter Topology Asymptotics in
theorem solution :
    (fun ε : ℝ => (∑' n : ℕ, (n : ℝ) * Real.exp (-ε * n)) - (1 / ε ^ 2 - 1 / 12))
      =O[𝓝[>] 0] (fun ε : ℝ => ε) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
  obtain ⟨h0, h1⟩ := hε
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h0, one_mul]
  have hxpos : 0 < Real.exp (-ε) := Real.exp_pos _
  have hxlt : Real.exp (-ε) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hsum : ∑' n : ℕ, (n : ℝ) * Real.exp (-ε * n)
      = Real.exp (-ε) / (1 - Real.exp (-ε)) ^ 2 := by
    have : ∀ n : ℕ, Real.exp (-ε * n) = Real.exp (-ε) ^ n := fun n => by
      rw [← Real.exp_nat_mul]; ring_nf
    simp_rw [this]
    exact tsum_coe_mul_geometric_of_norm_lt_one
      (by rw [Real.norm_eq_abs, abs_of_pos hxpos]; exact hxlt)
  rw [hsum, Real.exp_neg]
  set e := Real.exp ε with he_def
  have he1 : ε + 1 ≤ e := Real.add_one_le_exp ε
  have hepos : 0 < e := Real.exp_pos ε
  have hb := Real.exp_bound (x := ε) (n := 5) (by rw [abs_of_pos h0]; linarith) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, abs_of_pos h0] at hb
  norm_num at hb
  set t := (e - (1 + ε + ε ^ 2 / 2 + ε ^ 3 / 6 + ε ^ 4 / 24)) / ε ^ 5 with ht_def
  have hε5 : 0 < ε ^ 5 := by positivity
  have het : e = 1 + ε + ε ^ 2 / 2 + ε ^ 3 / 6 + ε ^ 4 / 24 + ε ^ 5 * t := by
    rw [ht_def]; field_simp; ring
  have htb : |t| ≤ 1 / 100 := by
    rw [ht_def, abs_div, abs_of_pos hε5, div_le_iff₀ hε5]
    rw [← he_def] at hb
    linarith [hb]
  have hQ := dc97380a_Q_bound ε t h0 h1 htb
  have hy : ε ≤ e - 1 := by linarith
  have hy0 : 0 < e - 1 := by linarith
  have key : e⁻¹ / (1 - e⁻¹) ^ 2 - (1 / ε ^ 2 - 1 / 12)
      = (12 * ε ^ 2 * e - 12 * (e - 1) ^ 2 + ε ^ 2 * (e - 1) ^ 2) / (12 * ε ^ 2 * (e - 1) ^ 2) := by
    have hne : e - 1 ≠ 0 := hy0.ne'
    have h1e : 1 - e⁻¹ = (e - 1) / e := by field_simp
    rw [h1e]
    field_simp
    ring
  have hN : 12 * ε ^ 2 * e - 12 * (e - 1) ^ 2 + ε ^ 2 * (e - 1) ^ 2
      = ε ^ 6 * (-12 * ε ^ 4 * t ^ 2 - 24 * t + ε ^ 6 * t ^ 2 - 2 * ε ^ 2 * t + ε ^ 4 * t / 3 + 1 / 4
      + ε ^ 5 * t / 12 + ε / 12 + 7 * ε ^ 2 / 144 + ε ^ 3 / 72 + ε ^ 4 / 576) := by
    rw [het]; ring
  rw [key, hN, abs_div, abs_mul, abs_of_pos (by positivity : (0:ℝ) < ε ^ 6),
    abs_of_pos (by positivity : (0:ℝ) < 12 * ε ^ 2 * (e - 1) ^ 2), div_le_iff₀ (by positivity)]
  have hsq : ε ^ 2 ≤ (e - 1) ^ 2 := by nlinarith
  have h6 : ε ^ 6 ≤ ε ^ 5 := pow_le_pow_of_le_one h0.le h1.le (by norm_num)
  have : ε ^ 6 * |(-12 * ε ^ 4 * t ^ 2 - 24 * t + ε ^ 6 * t ^ 2 - 2 * ε ^ 2 * t + ε ^ 4 * t / 3 + 1 / 4
      + ε ^ 5 * t / 12 + ε / 12 + 7 * ε ^ 2 / 144 + ε ^ 3 / 72 + ε ^ 4 / 576)| ≤ ε ^ 6 := by
    have := mul_le_mul_of_nonneg_left hQ (by positivity : (0:ℝ) ≤ ε ^ 6)
    linarith
  have h3 : ε ^ 5 ≤ ε * (12 * ε ^ 2 * (e - 1) ^ 2) := by
    have : ε ^ 3 * ε ^ 2 ≤ ε ^ 3 * (e - 1) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    nlinarith
  linarith
