-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P03.lemma17_smallWeight
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:11:10.784035+00:00
-- url     : https://prove2.me/submissions/2a7c7e58-005a-4773-8802-f1b26f925c4e

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03
noncomputable section

open QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace
attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

theorem solution (e eta alpha beta xhat bhat : ℝ)
    (he : 0 < e) (heta : 0 < eta) (ha : |alpha| ≤ eta)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1)
    (hx : |xhat - alpha * beta| < eta * e) (hb : |bhat - beta| < e) :
    beta * |smallWeightFilter e xhat bhat - alpha| ^ 2 ≤ 3 * eta ^ 2 * e := by
  have ha2 : alpha ^ 2 ≤ eta ^ 2 := by
    rw [← sq_abs alpha]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  have hb' := abs_lt.mp hb
  unfold smallWeightFilter
  split_ifs with h
  · rw [zero_sub, abs_neg, sq_abs]
    have : beta ≤ 3 * e := by linarith
    nlinarith [sq_nonneg alpha]
  · push_neg at h
    have hbpos : 0 < bhat := by linarith
    set D := xhat / bhat - alpha with hD
    have hDb : D * bhat = (xhat - alpha * beta) - alpha * (bhat - beta) := by
      rw [hD]; field_simp; ring
    have h1 : |D| * bhat ≤ 2 * eta * e := by
      have := abs_sub (xhat - alpha * beta) (alpha * (bhat - beta))
      rw [← hDb, abs_mul, abs_of_pos hbpos, abs_mul] at this
      have h2 : |alpha| * |bhat - beta| ≤ eta * e :=
        mul_le_mul ha hb.le (abs_nonneg _) heta.le
      linarith
    have h3 : (|D| * bhat) ^ 2 ≤ (2 * eta * e) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h4 : 4 * e * beta ≤ 3 * bhat ^ 2 := by nlinarith
    have h5 : beta * |D| ^ 2 * bhat ^ 2 ≤ 3 * eta ^ 2 * e * bhat ^ 2 := by
      have : beta * (|D| * bhat) ^ 2 ≤ beta * (2 * eta * e) ^ 2 :=
        mul_le_mul_of_nonneg_left h3 hb0
      have h6 : beta * (2 * eta * e) ^ 2 ≤ 3 * eta ^ 2 * e * bhat ^ 2 := by
        have : 0 ≤ eta ^ 2 * e := by positivity
        nlinarith
      nlinarith
    exact le_of_mul_le_mul_right h5 (by positivity)

end
