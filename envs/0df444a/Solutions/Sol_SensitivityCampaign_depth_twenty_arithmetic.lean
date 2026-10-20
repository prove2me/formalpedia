-- Prove2me | solution 1 for SensitivityCampaign.depth_twenty_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-20T03:03:47.30081+00:00
-- url     : https://prove2.me/submissions/90bacb14-31cc-4336-9d40-01983e4bb66c

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- An exact certificate for the unresolved depth-20 arithmetic target. -/
theorem solution :
    let M : ℕ := 9 ^ 21
    ((2 * (20 + 2) * M ^ 21 : ℕ) : ℝ) ^ (2.006470828 : ℝ) ≤
      ((M ^ 2 * (2 * M ^ 2 + 1) ^ 20 : ℕ) : ℝ) := by
  have h3nat : (3 : ℕ) ^ 10946 ≤ 2 ^ 17349 := by decide
  have h11nat : (11 : ℕ) ^ 4856 ≤ 2 ^ 16799 := by decide
  have h3real : (3 : ℝ) ^ 10946 ≤ (2 : ℝ) ^ 17349 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (Nat.cast_le.mpr h3nat : (((3 : ℕ) ^ 10946 : ℕ) : ℝ) ≤ (((2 : ℕ) ^ 17349 : ℕ) : ℝ))
  have h11real : (11 : ℝ) ^ 4856 ≤ (2 : ℝ) ^ 16799 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (Nat.cast_le.mpr h11nat : (((11 : ℕ) ^ 4856 : ℕ) : ℝ) ≤ (((2 : ℕ) ^ 16799 : ℕ) : ℝ))
  have h3 := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 3) 10946) h3real
  have h11 := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 11) 4856) h11real
  rw [Real.log_pow, Real.log_pow] at h3 h11
  norm_num only [Nat.cast_ofNat] at h3 h11
  have h2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  dsimp only
  let M : ℕ := 9 ^ 21
  change ((44 * M ^ 21 : ℕ) : ℝ) ^ (2.006470828 : ℝ) ≤
    ((M ^ 2 * (2 * M ^ 2 + 1) ^ 20 : ℕ) : ℝ)
  have hM : 0 < M := Nat.pow_pos (by decide : 0 < (9 : ℕ))
  have hA : 0 < ((44 * M ^ 21 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.mul_pos (by decide : 0 < (44 : ℕ)) (Nat.pow_pos hM))
  have hC : 0 < (2 : ℝ) ^ 20 * (3 : ℝ) ^ 1764 :=
    mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) 20)
      (pow_pos (by norm_num : (0 : ℝ) < 3) 1764)
  have hAeq : ((44 * M ^ 21 : ℕ) : ℝ) =
      (2 : ℝ) ^ 2 * 11 * (3 : ℝ) ^ 882 := by
    simp only [M, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
    change (44 : ℝ) * (3 : ℝ) ^ 882 = _
    rw [show (2 : ℝ) ^ 2 * 11 = 44 by norm_num]
  have hlog : Real.log (((44 * M ^ 21 : ℕ) : ℝ) ^ (2.006470828 : ℝ)) ≤
      Real.log ((2 : ℝ) ^ 20 * (3 : ℝ) ^ 1764) := by
    rw [Real.log_rpow hA, hAeq,
      Real.log_mul
        (mul_ne_zero (pow_ne_zero 2 (by norm_num : (2 : ℝ) ≠ 0))
          (by norm_num : (11 : ℝ) ≠ 0))
        (pow_ne_zero 882 (by norm_num : (3 : ℝ) ≠ 0)),
      Real.log_mul (pow_ne_zero 2 (by norm_num : (2 : ℝ) ≠ 0))
        (by norm_num : (11 : ℝ) ≠ 0),
      Real.log_mul (pow_ne_zero 20 (by norm_num : (2 : ℝ) ≠ 0))
        (pow_ne_zero 1764 (by norm_num : (3 : ℝ) ≠ 0))]
    simp only [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [h3, h11, h2]
  have hmain : ((44 * M ^ 21 : ℕ) : ℝ) ^ (2.006470828 : ℝ) ≤
      (2 : ℝ) ^ 20 * (3 : ℝ) ^ 1764 :=
    (Real.log_le_log_iff (Real.rpow_pos_of_pos hA _) hC).mp hlog
  have hbase : (2 : ℝ) ^ 20 * (3 : ℝ) ^ 1764 ≤
      ((M ^ 2 * (2 * M ^ 2 + 1) ^ 20 : ℕ) : ℝ) := by
    have heq : (2 : ℝ) ^ 20 * (3 : ℝ) ^ 1764 =
        ((M ^ 2 * (2 * M ^ 2) ^ 20 : ℕ) : ℝ) := by
      simp only [M, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      simp only [show (9 : ℝ) = 3 ^ 2 by norm_num, mul_pow, ← pow_mul]
      change (2 : ℝ) ^ 20 * (3 : ℝ) ^ 1764 =
        (3 : ℝ) ^ 84 * ((2 : ℝ) ^ 20 * (3 : ℝ) ^ 1680)
      rw [mul_left_comm, ← pow_add]
    rw [heq]
    exact Nat.cast_le.mpr (Nat.mul_le_mul_left (M ^ 2)
      (Nat.pow_le_pow_left (Nat.le_succ _) 20))
  exact hmain.trans hbase
