-- Prove2me | solution 1 for QuantumLinSys.Chebyshev.eq_89
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:25:08.564249+00:00
-- url     : https://prove2.me/submissions/13c711ee-7c3a-4705-81a0-8d17483258de

import Mathlib
import Definitions.Def_QuantumLinSys_Chebyshev_Setting
open QuantumLinSys.Chebyshev

theorem solution (b j : ℕ) : coeff b j ≤ Real.exp (-((j : ℝ) ^ 2) / b) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have : Finset.Icc (j + 1) 0 = ∅ := Finset.Icc_eq_empty (by omega)
    simp only [coeff, this, Finset.sum_empty, zero_div]
    positivity
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  set t : ℝ := 2 * j / b with ht
  have ht0 : 0 ≤ t := by positivity
  set g : ℕ → ℝ := fun k => ((2 * b).choose k : ℝ) * Real.exp (t * ((k : ℝ) - b)) with hg
  have hg0 : ∀ k, 0 ≤ g k := fun k => by simp only [hg]; positivity
  -- moment generating function
  have hmgf : ∑ k ∈ Finset.range (2 * b + 1), g k = (2 * Real.cosh (t / 2)) ^ (2 * b) := by
    rw [Real.cosh_eq]
    have h2 : 2 * ((Real.exp (t / 2) + Real.exp (-(t / 2))) / 2)
        = Real.exp (t / 2) + Real.exp (-(t / 2)) := by ring
    rw [h2, add_pow]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ 2 * b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    simp only [hg]
    rw [show t * ((k : ℝ) - b) = (k : ℝ) * (t / 2) + ((2 * b - k : ℕ) : ℝ) * (-(t / 2)) by
      rw [Nat.cast_sub hk']; push_cast; ring]
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul]
    ring
  have hcosh : (2 * Real.cosh (t / 2)) ^ (2 * b)
      ≤ 2 ^ (2 * b) * Real.exp ((b : ℝ) * t ^ 2 / 4) := by
    calc (2 * Real.cosh (t / 2)) ^ (2 * b)
        ≤ (2 * Real.exp ((t / 2) ^ 2 / 2)) ^ (2 * b) := by
          apply pow_le_pow_left₀ (by positivity)
          exact mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq _) (by norm_num)
      _ = 2 ^ (2 * b) * Real.exp ((b : ℝ) * t ^ 2 / 4) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 2
          push_cast
          ring
  -- tail bound
  have htail : ∑ i ∈ Finset.Icc (j + 1) b, ((2 * b).choose (b + i) : ℝ)
      ≤ Real.exp (-(t * j)) * ∑ k ∈ Finset.range (2 * b + 1), g k := by
    calc ∑ i ∈ Finset.Icc (j + 1) b, ((2 * b).choose (b + i) : ℝ)
        ≤ ∑ i ∈ Finset.Icc (j + 1) b, Real.exp (-(t * j)) * g (b + i) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hij : (j : ℝ) ≤ i := by
            have := (Finset.mem_Icc.mp hi).1
            exact_mod_cast (by omega : j ≤ i)
          simp only [hg]
          have hexp : 1 ≤ Real.exp (-(t * j)) * Real.exp (t * (((b + i : ℕ) : ℝ) - b)) := by
            rw [← Real.exp_add]
            apply Real.one_le_exp
            push_cast
            nlinarith
          have hc : (0 : ℝ) ≤ ((2 * b).choose (b + i) : ℝ) := by positivity
          nlinarith
      _ = Real.exp (-(t * j)) * ∑ i ∈ Finset.Icc (j + 1) b, g (b + i) := by
          rw [Finset.mul_sum]
      _ ≤ Real.exp (-(t * j)) * ∑ k ∈ Finset.range (2 * b + 1), g k := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          rw [← Finset.sum_image (f := g) (s := Finset.Icc (j + 1) b) (g := fun i => b + i)
            (fun x _ y _ h => by simpa using h)]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
            have := (Finset.mem_Icc.mp hi).2
            exact Finset.mem_range.mpr (by omega)
          · intro k _ _; exact hg0 k
  have hpos : (0 : ℝ) < 2 ^ (2 * b) := by positivity
  unfold coeff
  rw [div_le_iff₀ hpos]
  calc ∑ i ∈ Finset.Icc (j + 1) b, ((2 * b).choose (b + i) : ℝ)
      ≤ Real.exp (-(t * j)) * (2 ^ (2 * b) * Real.exp ((b : ℝ) * t ^ 2 / 4)) := by
        refine htail.trans ?_
        rw [hmgf]
        exact mul_le_mul_of_nonneg_left hcosh (Real.exp_pos _).le
    _ = Real.exp (-((j : ℝ) ^ 2) / b) * 2 ^ (2 * b) := by
        rw [mul_left_comm, ← Real.exp_add, mul_comm]
        congr 2
        rw [ht]
        field_simp
        ring
