-- Prove2me | solution 1 for SubexpPermanent.Main.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T13:30:11.810785+00:00
-- url     : https://prove2.me/submissions/bd62b552-67e8-4f6c-ba31-b4c2e87f94da

import Mathlib

set_option autoImplicit false

/-- Lemma A.2: if `√(z/t)` is used to compare `log (z + e)` with `log t + 1`, the squared
logarithmic loss is absorbed by `2z`. -/
theorem solution (t b z : ℝ) (ht : 1 ≤ t) (hb : 0 ≤ b) (hz : 0 ≤ z) :
    t * (b + Real.log (z + Real.exp 1)) ^ 2 ≤
      2 * t * (b + Real.log t + 1) ^ 2 + 2 * z := by
  have htpos : 0 < t := by linarith
  have hzdiv : 0 ≤ z / t := div_nonneg hz htpos.le
  set s : ℝ := Real.sqrt (z / t) with hs
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = z / t := Real.sq_sqrt hzdiv
  have hzs : t * s ^ 2 = z := by
    rw [hs_sq]
    field_simp
  have hexp3 : 1 + s + s ^ 2 / 2 ≤ Real.exp s := by
    have h := Real.sum_le_exp_of_nonneg hs_nonneg 3
    simpa [Finset.sum_range_succ] using h
  have hexp_ge : Real.exp 1 + s ^ 2 ≤ Real.exp (s + 1) := by
    have h1 : Real.exp 1 * (1 + s + s ^ 2 / 2) ≤ Real.exp (s + 1) := by
      rw [Real.exp_add, mul_comm (Real.exp s) (Real.exp 1)]
      exact mul_le_mul_of_nonneg_left hexp3 (Real.exp_pos 1).le
    have h2 : Real.exp 1 + s ^ 2 ≤ Real.exp 1 * (1 + s + s ^ 2 / 2) := by
      have he : (0 : ℝ) ≤ Real.exp 1 / 2 - 1 := by linarith [Real.exp_one_gt_two]
      have hterm1 : 0 ≤ Real.exp 1 * s := mul_nonneg (Real.exp_pos 1).le hs_nonneg
      have hterm2 : 0 ≤ (Real.exp 1 / 2 - 1) * s ^ 2 := mul_nonneg he (sq_nonneg s)
      nlinarith [hterm1, hterm2]
    exact h2.trans h1
  have hze : z + Real.exp 1 ≤ t * Real.exp 1 * Real.exp s := by
    have hmul : t * (Real.exp 1 + s ^ 2) ≤ t * Real.exp (s + 1) :=
      mul_le_mul_of_nonneg_left hexp_ge htpos.le
    have hze' : t * (Real.exp 1 + s ^ 2) = t * Real.exp 1 + z := by
      rw [mul_add, hzs]
    have hte : t * Real.exp (s + 1) = t * Real.exp 1 * Real.exp s := by
      rw [Real.exp_add, mul_comm (Real.exp s) (Real.exp 1), mul_assoc]
    rw [hze', hte] at hmul
    have hte1 : Real.exp 1 ≤ t * Real.exp 1 := by
      calc Real.exp 1 = 1 * Real.exp 1 := (one_mul _).symm
        _ ≤ t * Real.exp 1 := mul_le_mul_of_nonneg_right ht (Real.exp_pos 1).le
    linarith
  have hL : Real.log (z + Real.exp 1) ≤ Real.log t + 1 + s := by
    have hpos : 0 < z + Real.exp 1 := by positivity
    have hlog : Real.log (z + Real.exp 1) ≤ Real.log (t * Real.exp 1 * Real.exp s) :=
      Real.log_le_log hpos hze
    have hlogeq : Real.log (t * Real.exp 1 * Real.exp s) = Real.log t + 1 + s := by
      rw [Real.log_mul (mul_ne_zero htpos.ne' (Real.exp_pos 1).ne') (Real.exp_pos s).ne']
      rw [Real.log_mul htpos.ne' (Real.exp_pos 1).ne']
      rw [Real.log_exp, Real.log_exp]
    rwa [hlogeq] at hlog
  have hLpos : 0 ≤ Real.log (z + Real.exp 1) :=
    (Real.log_pos (by linarith [Real.exp_one_gt_two, hz])).le
  have hsq_le : (b + Real.log (z + Real.exp 1)) ^ 2 ≤
      (b + Real.log t + 1 + s) ^ 2 :=
    pow_le_pow_left₀ (by linarith [hb, hLpos]) (by linarith [hL]) 2
  have hstep1 : t * (b + Real.log (z + Real.exp 1)) ^ 2 ≤
      t * (b + Real.log t + 1 + s) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq_le htpos.le
  have hstep2 : t * (b + Real.log t + 1 + s) ^ 2 ≤
      2 * t * (b + Real.log t + 1) ^ 2 + 2 * z := by
    have hsquare : 0 ≤ t * (b + Real.log t + 1 - s) ^ 2 :=
      mul_nonneg htpos.le (sq_nonneg _)
    nlinarith [hsquare, hzs]
  linarith [hstep1, hstep2]
