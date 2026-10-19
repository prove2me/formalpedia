-- Prove2me | solution 1 for QAlgorithms.Nannicini.sinSq_angle_error
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T07:30:04.644906+00:00
-- url     : https://prove2.me/submissions/e93d7dcb-5d2f-4dcd-b359-b972094ed72b

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

private lemma sin_sq_error (θ d : ℝ) :
    |Real.sin (θ + d) ^ 2 - Real.sin θ ^ 2| ≤
      2 * |d| * |Real.sin θ * Real.cos θ| + |d| ^ 2 := by
  have ht := Real.sin_sq_add_cos_sq θ
  have hd := Real.sin_sq_add_cos_sq d
  have hid : Real.sin (θ + d) ^ 2 - Real.sin θ ^ 2 =
      (Real.sin θ * Real.cos θ) * Real.sin (2 * d) +
      (Real.cos θ ^ 2 - Real.sin θ ^ 2) * Real.sin d ^ 2 := by
    rw [Real.sin_add, Real.sin_two_mul]
    nlinarith [sq_nonneg (Real.sin θ * Real.sin d)]
  have hc : |Real.cos θ ^ 2 - Real.sin θ ^ 2| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ)]
  have hsin : |Real.sin (2 * d)| ≤ 2 * |d| := by
    simpa [abs_mul] using Real.abs_sin_le_abs (x := 2 * d)
  have hsq : Real.sin d ^ 2 ≤ |d| ^ 2 := by
    have h := Real.abs_sin_le_abs (x := d)
    simpa only [← sq, sq_abs] using
      mul_self_le_mul_self (abs_nonneg (Real.sin d)) h
  rw [hid]
  calc
    _ ≤ |(Real.sin θ * Real.cos θ) * Real.sin (2 * d)| +
        |(Real.cos θ ^ 2 - Real.sin θ ^ 2) * Real.sin d ^ 2| := abs_add_le _ _
    _ = |Real.sin θ * Real.cos θ| * |Real.sin (2 * d)| +
        |Real.cos θ ^ 2 - Real.sin θ ^ 2| * Real.sin d ^ 2 := by
      simp only [abs_mul, abs_pow, sq_abs]
    _ ≤ |Real.sin θ * Real.cos θ| * (2 * |d|) + 1 * |d| ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hsin (abs_nonneg _))
        (mul_le_mul hc hsq (sq_nonneg _) (by norm_num))
    _ = _ := by ring

theorem solution (θ θt ε : ℝ) (_hθ0 : 0 ≤ θ) (_hθ1 : θ ≤ 2 * Real.pi)
    (_hθt0 : 0 ≤ θt) (_hθt1 : θt ≤ 2 * Real.pi) (h : |θ - θt| ≤ ε) :
    |Real.sin θ ^ 2 - Real.sin θt ^ 2| ≤
      2 * ε * Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) + ε ^ 2 := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans h
  have hd : |θt - θ| ≤ ε := by simpa only [abs_sub_comm] using h
  have hr : Real.sqrt (Real.sin θ ^ 2 * (1 - Real.sin θ ^ 2)) =
      |Real.sin θ * Real.cos θ| := by
    rw [show 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq θ], ← mul_pow, Real.sqrt_sq_eq_abs]
  rw [hr, abs_sub_comm]
  have hb := sin_sq_error θ (θt - θ)
  rw [add_sub_cancel] at hb
  apply hb.trans
  have hm := mul_le_mul_of_nonneg_right hd (abs_nonneg (Real.sin θ * Real.cos θ))
  have hs : |θt - θ| ^ 2 ≤ ε ^ 2 := by nlinarith [abs_nonneg (θt - θ)]
  nlinarith
