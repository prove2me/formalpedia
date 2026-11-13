-- Prove2me | solution 1 for ThreshRankBIS.eq_13_14
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-13T02:09:59.177699+00:00
-- url     : https://prove2.me/submissions/b210a1db-c9bf-4f73-936a-32f1d783bb5a

import Mathlib
set_option autoImplicit false
open Finset

theorem solution :
    (∀ (m : ℕ) (L z : ℝ), 0 ≤ L → 0 < z → z ≤ 1 →
      (∑ j ∈ range (min m ⌊L⌋₊ + 1), (m.choose j : ℝ)) ≤ z ^ (-L) * (1 + z) ^ m ∧
        z ^ (-L) * (1 + z) ^ m ≤ z ^ (-L) * Real.exp (m * z)) ∧
    (∀ (m : ℕ) (M h : ℝ), (m : ℝ) ≤ M → 0 < h → h ≤ M →
      (∑ j ∈ range (min m ⌊h⌋₊ + 1), (m.choose j : ℝ)) ≤
        Real.exp (h * Real.log (Real.exp 1 * M / h))) := by
  have key : ∀ (m : ℕ) (L z : ℝ), 0 ≤ L → 0 < z → z ≤ 1 →
      (∑ j ∈ range (min m ⌊L⌋₊ + 1), (m.choose j : ℝ)) ≤ z ^ (-L) * (1 + z) ^ m ∧
        z ^ (-L) * (1 + z) ^ m ≤ z ^ (-L) * Real.exp (m * z) := by
    intro m L z hL hz hz1
    have hzL : 0 < z ^ (-L) := Real.rpow_pos_of_pos hz _
    constructor
    · have hbin : (1 + z) ^ m = ∑ j ∈ range (m + 1), (m.choose j : ℝ) * z ^ j := by
        rw [add_comm, add_pow]
        refine sum_congr rfl fun j _ => ?_
        simp [mul_comm]
      rw [hbin, mul_sum]
      calc (∑ j ∈ range (min m ⌊L⌋₊ + 1), (m.choose j : ℝ))
          ≤ ∑ j ∈ range (min m ⌊L⌋₊ + 1), z ^ (-L) * ((m.choose j : ℝ) * z ^ j) := by
            refine sum_le_sum fun j hj => ?_
            have hjL : (j : ℝ) ≤ L := by
              have hj' : j ≤ ⌊L⌋₊ := by
                have := mem_range.mp hj
                omega
              exact (Nat.le_floor_iff hL).mp hj'
            have h1 : (1 : ℝ) ≤ z ^ (-L) * z ^ j := by
              rw [← Real.rpow_natCast, ← Real.rpow_add hz]
              exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hz hz1 (by linarith)
            calc (m.choose j : ℝ) = (m.choose j : ℝ) * 1 := (mul_one _).symm
              _ ≤ (m.choose j : ℝ) * (z ^ (-L) * z ^ j) :=
                  mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
              _ = z ^ (-L) * ((m.choose j : ℝ) * z ^ j) := by ring
        _ ≤ ∑ j ∈ range (m + 1), z ^ (-L) * ((m.choose j : ℝ) * z ^ j) := by
            refine sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) ?_
            intro j _ _
            positivity
    · apply mul_le_mul_of_nonneg_left _ hzL.le
      calc (1 + z) ^ m ≤ (Real.exp z) ^ m :=
            pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp z]) m
        _ = Real.exp (m * z) := by rw [← Real.exp_nat_mul]
  refine ⟨key, ?_⟩
  intro m M h hmM hh hhM
  have hM : 0 < M := lt_of_lt_of_le hh hhM
  have hz : 0 < h / M := div_pos hh hM
  have hz1 : h / M ≤ 1 := (div_le_one hM).mpr hhM
  obtain ⟨k1, k2⟩ := key m h (h / M) hh.le hz hz1
  refine (k1.trans k2).trans ?_
  have e1 : (h / M) ^ (-h) = Real.exp (h * Real.log (M / h)) := by
    rw [Real.rpow_def_of_pos hz, Real.log_div hh.ne' hM.ne', Real.log_div hM.ne' hh.ne']
    congr 1
    ring
  have e2 : Real.log (Real.exp 1 * M / h) = 1 + Real.log (M / h) := by
    rw [mul_div_assoc, Real.log_mul (Real.exp_pos 1).ne' (div_pos hM hh).ne', Real.log_exp]
  rw [e1, e2, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h3 : (m : ℝ) * (h / M) ≤ h := by
    rw [← mul_div_assoc, div_le_iff₀ hM]
    linarith [mul_le_mul_of_nonneg_left hmM hh.le]
  linarith
