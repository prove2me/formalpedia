-- Prove2me | solution 1 for RhinViola.selectedIndexErrorLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T21:45:48.598419+00:00
-- url     : https://prove2.me/submissions/bc0e1d6e-f166-4504-a92d-31b3e297e17e

import Theorems.Thm_RhinViola_integerLinearFormScaledLowerBound
import Theorems.Thm_RhinViola_selectedIndexMakesLinearFormSmall
import Mathlib.Tactic

theorem solution
    (α f u v w : ℝ) (a b p : ℤ) (q n : ℕ)
    (hq : 0 < q) (hb : b ≠ 0) (hu : 0 < u)
    (hf : f = (a : ℝ) - (b : ℝ) * α)
    (hn : Real.log (2 * (q : ℝ)) / u ≤ (n : ℝ))
    (hf_upper : |f| ≤ Real.exp (-(u * (n : ℝ))))
    (hf_lower : Real.exp (-(v * (n : ℝ))) ≤ |f|)
    (hb_upper : |(b : ℝ)| ≤ Real.exp (w * (n : ℝ))) :
    Real.exp (-((v + w) * (n : ℝ))) ≤
      |α - (p : ℝ) / (q : ℝ)| := by
  have hqR : 0 < (q : ℝ) := by
    exact_mod_cast hq
  have hq0 : 0 ≤ (q : ℝ) := hqR.le
  have hsmall : (q : ℝ) * |f| ≤ (1 : ℝ) / 2 :=
    RhinViola.selectedIndexMakesLinearFormSmall
      u f q n hu hq hn hf_upper
  have hqL :
      (q : ℝ) * Real.exp (-(v * (n : ℝ))) ≤ (1 : ℝ) / 2 := by
    exact le_trans (mul_le_mul_of_nonneg_left hf_lower hq0) hsmall
  have hscaled :=
    RhinViola.integerLinearFormScaledLowerBound
      α f (Real.exp (-(v * (n : ℝ)))) (Real.exp (w * (n : ℝ)))
      a b p q hq hb hf hsmall hf_lower hb_upper
  have hmin :
      min ((q : ℝ) * Real.exp (-(v * (n : ℝ)))) ((1 : ℝ) / 2) =
        (q : ℝ) * Real.exp (-(v * (n : ℝ))) :=
    min_eq_left hqL
  rw [hmin] at hscaled
  have hscaled' :
      (q : ℝ) * Real.exp (-(v * (n : ℝ))) ≤
        (q : ℝ) *
          (Real.exp (w * (n : ℝ)) *
            |α - (p : ℝ) / (q : ℝ)|) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hcancel :
      Real.exp (-(v * (n : ℝ))) ≤
        Real.exp (w * (n : ℝ)) *
          |α - (p : ℝ) / (q : ℝ)| :=
    le_of_mul_le_mul_left hscaled' hqR
  have hmul :=
    mul_le_mul_of_nonneg_left hcancel (Real.exp_pos (-(w * (n : ℝ)))).le
  calc
    Real.exp (-((v + w) * (n : ℝ))) =
        Real.exp (-(w * (n : ℝ))) *
          Real.exp (-(v * (n : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(w * (n : ℝ))) *
          (Real.exp (w * (n : ℝ)) *
            |α - (p : ℝ) / (q : ℝ)|) := hmul
    _ = (Real.exp (-(w * (n : ℝ))) *
          Real.exp (w * (n : ℝ))) *
            |α - (p : ℝ) / (q : ℝ)| := by ring
    _ = |α - (p : ℝ) / (q : ℝ)| := by
      have hz : -(w * (n : ℝ)) + w * (n : ℝ) = 0 := by ring
      rw [← Real.exp_add, hz, Real.exp_zero, one_mul]
