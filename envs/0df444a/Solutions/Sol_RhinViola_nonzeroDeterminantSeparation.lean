-- Prove2me | solution 1 for RhinViola.nonzeroDeterminantSeparation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T10:39:50.550764+00:00
-- url     : https://prove2.me/submissions/551ff352-933d-473a-a42b-0118c6881ade

import Mathlib.Tactic
import Mathlib.Data.Int.Cast.Lemmas

theorem solution
    (α f : ℝ) (a b p : ℤ) (q : ℕ)
    (hq : 0 < q)
    (hf : f = (a : ℝ) - (b : ℝ) * α)
    (hsmall : (q : ℝ) * |f| ≤ (1 : ℝ) / 2)
    (hdet : (q : ℤ) * a ≠ p * b) :
    (1 : ℝ) / 2 ≤ |(b : ℝ)| * (q : ℝ) *
      |α - (p : ℝ) / (q : ℝ)| := by
  have hqR : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  let D : ℤ := (q : ℤ) * a - p * b
  have hDne : D ≠ 0 := by
    dsimp [D]
    exact sub_ne_zero.mpr hdet
  have hDone : (1 : ℤ) ≤ |D| := Int.one_le_abs hDne
  have hDoneCast : (1 : ℝ) ≤ ((|D| : ℤ) : ℝ) := by
    exact_mod_cast hDone
  have hDoneR : (1 : ℝ) ≤ |(D : ℝ)| := by
    simpa only [Int.cast_abs] using hDoneCast
  have hid :
      (D : ℝ) =
        (q : ℝ) * f + (b : ℝ) * ((q : ℝ) * α - (p : ℝ)) := by
    dsimp [D]
    rw [hf]
    push_cast
    ring
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have htri :
      |(D : ℝ)| ≤
        (q : ℝ) * |f| +
          |(b : ℝ)| * |(q : ℝ) * α - (p : ℝ)| := by
    rw [hid]
    simpa only [abs_mul, abs_of_nonneg hq0] using
      (abs_add_le ((q : ℝ) * f)
        ((b : ℝ) * ((q : ℝ) * α - (p : ℝ))))

  have hhalf :
      (1 : ℝ) / 2 ≤ |(b : ℝ)| * |(q : ℝ) * α - (p : ℝ)| := by
    linarith
  have hrewrite :
      (q : ℝ) * α - (p : ℝ) =
        (q : ℝ) * (α - (p : ℝ) / (q : ℝ)) := by
    field_simp [hqR]
  have habs :
      |(q : ℝ) * α - (p : ℝ)| =
        (q : ℝ) * |α - (p : ℝ) / (q : ℝ)| := by
    rw [hrewrite, abs_mul, abs_of_pos]
    exact_mod_cast hq
  rw [habs] at hhalf
  simpa only [mul_assoc] using hhalf
