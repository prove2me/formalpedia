-- Prove2me | solution 1 for RhinViola.selectedIndexMakesLinearFormSmall
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T13:48:29.071857+00:00
-- url     : https://prove2.me/submissions/34046803-1384-4940-b370-a601d6b7db8a

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

theorem solution
    (u f : ℝ) (q n : ℕ)
    (hu : 0 < u) (hq : 0 < q)
    (hn : Real.log (2 * (q : ℝ)) / u ≤ (n : ℝ))
    (hf : |f| ≤ Real.exp (-(u * (n : ℝ)))) :
    (q : ℝ) * |f| ≤ (1 : ℝ) / 2 := by
  have hqR : 0 < (q : ℝ) := by
    exact_mod_cast hq
  have htwoq : 0 < (2 : ℝ) * (q : ℝ) := by
    positivity
  have hlog_le :
      Real.log (2 * (q : ℝ)) ≤ (n : ℝ) * u := by
    exact (div_le_iff₀ hu).mp hn
  have hexp :
      (2 : ℝ) * (q : ℝ) ≤ Real.exp (u * (n : ℝ)) := by
    have h := Real.exp_le_exp.mpr hlog_le
    rw [Real.exp_log htwoq] at h
    simpa [mul_comm] using h
  have hleft :
      (2 : ℝ) * (q : ℝ) * |f| ≤
        Real.exp (u * (n : ℝ)) * |f| :=
    mul_le_mul_of_nonneg_right hexp (abs_nonneg f)
  have hright :
      Real.exp (u * (n : ℝ)) * |f| ≤ 1 := by
    calc
      Real.exp (u * (n : ℝ)) * |f|
          ≤ Real.exp (u * (n : ℝ)) *
              Real.exp (-(u * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hf (Real.exp_pos _).le
      _ = 1 := by
        rw [← Real.exp_add]
        ring_nf
        simp
  have htwo :
      (2 : ℝ) * (q : ℝ) * |f| ≤ 1 :=
    le_trans hleft hright
  nlinarith
