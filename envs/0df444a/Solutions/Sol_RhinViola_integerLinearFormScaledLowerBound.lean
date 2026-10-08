-- Prove2me | solution 1 for RhinViola.integerLinearFormScaledLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T20:09:04.197869+00:00
-- url     : https://prove2.me/submissions/ede4d797-4c7d-4505-98bf-3e3f2359f271

import Theorems.Thm_RhinViola_integerLinearFormDichotomy
import Mathlib.Tactic

theorem solution
    (α f L U : ℝ) (a b p : ℤ) (q : ℕ)
    (hq : 0 < q) (hb : b ≠ 0)
    (hf : f = (a : ℝ) - (b : ℝ) * α)
    (hsmall : (q : ℝ) * |f| ≤ (1 : ℝ) / 2)
    (hL : L ≤ |f|) (hU : |(b : ℝ)| ≤ U) :
    min ((q : ℝ) * L) ((1 : ℝ) / 2) ≤
      U * (q : ℝ) * |α - (p : ℝ) / (q : ℝ)| := by
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have herr0 : 0 ≤ |α - (p : ℝ) / (q : ℝ)| := abs_nonneg _
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have habsb : |(b : ℝ)| ≠ 0 := abs_ne_zero.mpr hbR
  rcases RhinViola.integerLinearFormDichotomy
      α f a b p q hq hb hf hsmall with hzero | hsep
  · have hproduct :
        |f| = |(b : ℝ)| * |α - (p : ℝ) / (q : ℝ)| := by
      have hmul := (eq_div_iff habsb).mp hzero
      nlinarith
    calc
      min ((q : ℝ) * L) ((1 : ℝ) / 2) ≤ (q : ℝ) * L :=
        min_le_left _ _
      _ ≤ (q : ℝ) * |f| := mul_le_mul_of_nonneg_left hL hq0
      _ = |(b : ℝ)| * ((q : ℝ) * |α - (p : ℝ) / (q : ℝ)|) := by
        rw [hproduct]
        ring
      _ ≤ U * ((q : ℝ) * |α - (p : ℝ) / (q : ℝ)|) :=
        mul_le_mul_of_nonneg_right hU (mul_nonneg hq0 herr0)
      _ = U * (q : ℝ) * |α - (p : ℝ) / (q : ℝ)| := by ring
  · calc
      min ((q : ℝ) * L) ((1 : ℝ) / 2) ≤ (1 : ℝ) / 2 :=
        min_le_right _ _
      _ ≤ |(b : ℝ)| * (q : ℝ) * |α - (p : ℝ) / (q : ℝ)| := hsep
      _ = |(b : ℝ)| * ((q : ℝ) * |α - (p : ℝ) / (q : ℝ)|) := by ring
      _ ≤ U * ((q : ℝ) * |α - (p : ℝ) / (q : ℝ)|) :=
        mul_le_mul_of_nonneg_right hU (mul_nonneg hq0 herr0)
      _ = U * (q : ℝ) * |α - (p : ℝ) / (q : ℝ)| := by ring
