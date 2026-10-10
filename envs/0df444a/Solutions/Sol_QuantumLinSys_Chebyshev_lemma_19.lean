-- Prove2me | solution 1 for QuantumLinSys.Chebyshev.lemma_19
-- status  : ACCEPTED   (prove)
-- author  : @elem
-- created : 2026-10-09T22:01:47.125745+00:00
-- url     : https://prove2.me/submissions/05475d03-ac1b-47fb-b6bf-84bbab0d0678

import Mathlib
import Definitions.Def_QuantumLinSys_Chebyshev_Setting
import Theorems.Thm_QuantumLinSys_Chebyshev_lemma_18
import Theorems.Thm_QuantumLinSys_Chebyshev_eq_89

open QuantumLinSys.Chebyshev

open Finset

lemma coeff_nonneg' (b j : ℕ) : 0 ≤ coeff b j := by
  unfold coeff; positivity

lemma coeff_eq_zero_of_le' (b j : ℕ) (h : b ≤ j) : coeff b j = 0 := by
  unfold coeff
  rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, zero_div]

lemma abs_T_eval_le_one' (n : ℤ) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.T ℝ n).eval x| ≤ 1 := by
  have hx' : x = Real.cos (Real.arccos x) := (Real.cos_arccos hx.1 hx.2).symm
  rw [hx', Polynomial.Chebyshev.T_real_cos]
  exact Real.abs_cos_le_one _

theorem solution (b : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, |chebSum b (j0Of b ε + 1) x - fTamed b x| ≤ ε := by
  intro x hx
  rw [lemma_18 b x hx]
  set a : ℕ → ℝ := fun j =>
    (-1 : ℝ) ^ j * coeff b j * (Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)).eval x with ha
  have hcheb : ∀ m, chebSum b m x = 4 * ∑ j ∈ Finset.range m, a j := fun m => rfl
  rw [hcheb, hcheb]
  rcases le_or_gt (j0Of b ε + 1) b with hnb | hbn
  · rw [← Finset.sum_range_add_sum_Ico a hnb]
    have hb0 : 0 < b := by omega
    have hbpos : (0 : ℝ) < b := by exact_mod_cast hb0
    have hterm : ∀ j ∈ Finset.Ico (j0Of b ε + 1) b, |a j| ≤ ε / (4 * b) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have hj1 : (j0Of b ε : ℝ) + 1 ≤ j := by exact_mod_cast hj.1
      have hjpos : (0 : ℝ) < j := by linarith [Nat.cast_nonneg (α := ℝ) (j0Of b ε)]
      have hkey : Real.exp (-((j : ℝ) ^ 2) / b) ≤ ε / (4 * b) := by
        have hsj : Real.sqrt (b * Real.log (4 * b / ε)) < j := by
          have hfl := Nat.lt_floor_add_one (Real.sqrt (b * Real.log (4 * b / ε)))
          unfold j0Of at hj1; linarith
        have hsq : (b : ℝ) * Real.log (4 * b / ε) < (j : ℝ) ^ 2 := by
          rcases le_or_gt 0 ((b : ℝ) * Real.log (4 * b / ε)) with hnn | hneg
          · exact (Real.sqrt_lt' hjpos).mp hsj
          · nlinarith
        have hlt : -((j : ℝ) ^ 2) / b < -Real.log (4 * b / ε) := by
          rw [div_lt_iff₀ hbpos]; linarith
        calc Real.exp (-((j : ℝ) ^ 2) / b) ≤ Real.exp (-Real.log (4 * b / ε)) :=
              Real.exp_le_exp.mpr hlt.le
          _ = ε / (4 * b) := by
              rw [Real.exp_neg, Real.exp_log (by positivity)]
              field_simp
      calc |a j| = coeff b j * |(Polynomial.Chebyshev.T ℝ ((2 * j + 1 : ℕ) : ℤ)).eval x| := by
            rw [ha]; simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
              abs_of_nonneg (coeff_nonneg' b j)]
        _ ≤ coeff b j * 1 :=
            mul_le_mul_of_nonneg_left (abs_T_eval_le_one' _ _ hx) (coeff_nonneg' b j)
        _ = coeff b j := mul_one _
        _ ≤ Real.exp (-((j : ℝ) ^ 2) / b) := eq_89 b j
        _ ≤ ε / (4 * b) := hkey
    have hcard : ((b - (j0Of b ε + 1) : ℕ) : ℝ) ≤ b := by exact_mod_cast Nat.sub_le _ _
    calc |4 * ∑ j ∈ Finset.range (j0Of b ε + 1), a j -
          4 * (∑ j ∈ Finset.range (j0Of b ε + 1), a j + ∑ j ∈ Finset.Ico (j0Of b ε + 1) b, a j)|
        = 4 * |∑ j ∈ Finset.Ico (j0Of b ε + 1) b, a j| := by
          rw [show 4 * ∑ j ∈ Finset.range (j0Of b ε + 1), a j -
              4 * (∑ j ∈ Finset.range (j0Of b ε + 1), a j + ∑ j ∈ Finset.Ico (j0Of b ε + 1) b, a j)
              = -(4 * ∑ j ∈ Finset.Ico (j0Of b ε + 1) b, a j) by ring, abs_neg, abs_mul,
            abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      _ ≤ 4 * ∑ j ∈ Finset.Ico (j0Of b ε + 1) b, |a j| := by
          gcongr; exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ 4 * ∑ j ∈ Finset.Ico (j0Of b ε + 1) b, ε / (4 * b) := by
          gcongr with j hj; exact hterm j hj
      _ = 4 * (((b - (j0Of b ε + 1) : ℕ) : ℝ) * (ε / (4 * b))) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ 4 * ((b : ℝ) * (ε / (4 * b))) := by gcongr
      _ = ε := by field_simp
  · rw [← Finset.sum_range_add_sum_Ico a hbn.le]
    have hz : ∑ j ∈ Finset.Ico b (j0Of b ε + 1), a j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_Ico] at hj
      simp [ha, coeff_eq_zero_of_le' b j hj.1]
    rw [hz, add_zero, sub_self, abs_zero]
    exact hε.le

