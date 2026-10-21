-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.denominatorNonnegative
-- status  : ACCEPTED   (prove)
-- author  : @Yonghao Wang
-- created : 2026-10-21T03:30:21.329912+00:00
-- url     : https://prove2.me/submissions/5de6a8fb-4086-4f2d-aeb9-ee8d7cd19d19

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

open QAlgorithms.Papers.Independent.Information100.P32

theorem solution (m : Model) : 0 ≤ denominatorK m := by
  let x : ℝ := angleC m
  let y : ℝ := Real.cos (m.frequency * m.duration)
  let q : ℝ := 4 * Complex.normSq m.cA
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg (by norm_num) (Complex.normSq_nonneg m.cA)
  have hq1 : q ≤ 1 := by
    have hc := m.ancilla_physical.2.2
    dsimp [q]
    nlinarith [sq_nonneg (m.pA - 1 / 2)]
  have hx : |x| ≤ 1 := by
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hy : |y| ≤ 1 := by
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hxy : x * y ≤ |x| := by
    calc
      x * y ≤ |x * y| := le_abs_self _
      _ = |x| * |y| := abs_mul _ _
      _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left hy (abs_nonneg x)
      _ = |x| := mul_one _
  have hfactor : 0 ≤ 1 - (1 - q) * |x| := by
    nlinarith [mul_nonneg hq0 (abs_nonneg x)]
  have hprod : 0 ≤ (1 - |x|) * (1 - (1 - q) * |x|) :=
    mul_nonneg (sub_nonneg.mpr hx) hfactor
  have hsq : |x| ^ 2 = x ^ 2 := sq_abs x
  have hpoly : 0 ≤ 1 + (1 - q) * x ^ 2 - (2 - q) * |x| := by
    calc
      0 ≤ (1 - |x|) * (1 - (1 - q) * |x|) := hprod
      _ = 1 + (1 - q) * |x| ^ 2 - (2 - q) * |x| := by ring
      _ = 1 + (1 - q) * x ^ 2 - (2 - q) * |x| := by rw [hsq]
  have hcompare : (2 - q) * (x * y) ≤ (2 - q) * |x| :=
    mul_le_mul_of_nonneg_left hxy (by linarith)
  have hK : denominatorK m = 1 + (1 - q) * x ^ 2 - (2 - q) * (x * y) := by
    dsimp [denominatorK, denominatorD, differenceL, x, y, q]
    nlinarith [Real.sin_sq_add_cos_sq (m.frequency * m.duration)]
  rw [hK]
  linarith
