-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P47.flat_group_false_positives
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T02:34:20.838339+00:00
-- url     : https://prove2.me/submissions/9133b307-20cb-4615-a1f1-fdce9c2fb879

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open MeasureTheory Filter

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P47

open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)

open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)

open QAlgorithms.Papers.Independent.Information100.P48 (normalize)

open QAlgorithms.Papers.Independent.Information100.P62 (IsProjection)


theorem g53b_tr_nonneg {D : Type} [Fintype D] [DecidableEq D] (Q R : Matrix D D ℂ)
    (hQ : IsProjection Q) (hR : IsProjection R) : 0 ≤ (Q * R).trace.re := by
  have h1 : (Q * R).trace = ((Q * R)ᴴ * (Q * R)).trace := by
    rw [Matrix.conjTranspose_mul, hQ.1, hR.1]
    calc (Q * R).trace = (Q * Q * R * R).trace := by rw [hQ.2, Matrix.mul_assoc, hR.2]
      _ = (R * (Q * Q * R)).trace := by rw [Matrix.trace_mul_comm R]
      _ = (R * Q * (Q * R)).trace := by simp only [Matrix.mul_assoc]
  rw [h1]
  have := (Matrix.posSemidef_conjTranspose_mul_self (Q * R)).trace_nonneg
  exact (Complex.nonneg_iff.mp this).1

theorem g53b_proj_compl {D : Type} [Fintype D] [DecidableEq D] (R : Matrix D D ℂ)
    (hR : IsProjection R) : IsProjection (1 - R) := by
  refine ⟨by rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hR.1], ?_⟩
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hR.2]; simp

theorem g53b_tr_le {D : Type} [Fintype D] [DecidableEq D] (Q R : Matrix D D ℂ)
    (hQ : IsProjection Q) (hR : IsProjection R) : (Q * R).trace.re ≤ Q.trace.re := by
  have := g53b_tr_nonneg Q (1 - R) hQ (g53b_proj_compl R hR)
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Complex.sub_re] at this
  linarith

theorem g53b_bern (m : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    moreThanOneProbability m t ≤ (m : ℝ) * t := by
  unfold moreThanOneProbability
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -t by linarith) m
  have : 0 ≤ (m : ℝ) * t * (1 - t) ^ (m - 1) := by
    have : 0 ≤ 1 - t := by linarith
    positivity
  have e : (1 : ℝ) + -t = 1 - t := by ring
  rw [e] at hb
  nlinarith

/-- Lemma 5, PDF pp.17,22,24: finite-block rank formulation of the false-positive bound.
The m copies are the independent flat typical state before conditioning on Alice's success.
Any integer m below the displayed real group size is permitted, including zero. -/
theorem solution {D : Type} [Fintype D] [DecidableEq D]
    (P Py : Matrix D D ℂ) (hP : IsProjection P) (hPy : IsProjection Py)
    (n m : ℕ) (eps alpha delta dd c hF hFY : ℝ)
    (heps0 : 0 < eps) (heps1 : eps < 1) (halpha : 0 < alpha)
    (hdelta : 0 < delta) (hdd : 0 ≤ dd) (hc : 0 < c)
    (hrankP : (1 - eps) * (2 : ℝ) ^ ((n : ℝ) * (hF - c * delta)) ≤ P.trace.re)
    (hrankY : Py.trace.re ≤ (2 : ℝ) ^ ((n : ℝ) * (hFY + dd)))
    (hgroup : (m : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (hF - hFY - dd - c * delta - alpha))) :
    moreThanOneProbability m (effectProb Py (normalize P)) ≤
      (2 : ℝ) ^ (-alpha * n + 1) / (1 - eps) := by
  have hp0 : 0 < (1 - eps) * (2 : ℝ) ^ ((n : ℝ) * (hF - c * delta)) := by
    apply mul_pos (by linarith); positivity
  have hp : 0 < P.trace.re := lt_of_lt_of_le hp0 hrankP
  have ht : effectProb Py (normalize P) = (Py * P).trace.re / P.trace.re := by
    unfold effectProb QAlgorithms.Papers.Independent.Information100.P48.normalize
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← Complex.ofReal_inv,
      Complex.re_ofReal_mul]
    ring
  have hA0 := g53b_tr_nonneg Py P hPy hP
  have hA1 := g53b_tr_le Py P hPy hP
  have hA2 : (Py * P).trace.re ≤ P.trace.re := by
    rw [Matrix.trace_mul_comm]; exact g53b_tr_le P Py hP hPy
  have hY0 : 0 ≤ Py.trace.re := le_trans hA0 hA1
  set t := effectProb Py (normalize P) with htdef
  have t0 : 0 ≤ t := by rw [ht]; positivity
  have t1 : t ≤ 1 := by rw [ht, div_le_one hp]; exact hA2
  have t2 : t ≤ Py.trace.re / P.trace.re := by
    rw [ht]; exact div_le_div_of_nonneg_right hA1 hp.le
  refine le_trans (g53b_bern m t t0 t1) ?_
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have s1 : (m : ℝ) * t ≤ (m : ℝ) * Py.trace.re / P.trace.re := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left t2 hm0
  have s2 : (m : ℝ) * Py.trace.re ≤ (2 : ℝ) ^ ((n : ℝ) * (hF - c * delta - alpha)) := by
    have := mul_le_mul hgroup hrankY hY0 (by positivity)
    rw [← Real.rpow_add (by norm_num)] at this
    have e : (n : ℝ) * (hF - c * delta - alpha) =
        (n : ℝ) * (hF - hFY - dd - c * delta - alpha) + (n : ℝ) * (hFY + dd) := by ring
    rw [e]; exact this
  have s3 : (m : ℝ) * Py.trace.re / P.trace.re ≤
      (2 : ℝ) ^ ((n : ℝ) * (hF - c * delta - alpha)) /
        ((1 - eps) * (2 : ℝ) ^ ((n : ℝ) * (hF - c * delta))) := by
    calc (m : ℝ) * Py.trace.re / P.trace.re
        ≤ (2 : ℝ) ^ ((n : ℝ) * (hF - c * delta - alpha)) / P.trace.re :=
          div_le_div_of_nonneg_right s2 hp.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hp0 hrankP
  have s4 : (2 : ℝ) ^ ((n : ℝ) * (hF - c * delta - alpha)) /
        ((1 - eps) * (2 : ℝ) ^ ((n : ℝ) * (hF - c * delta))) =
      (2 : ℝ) ^ (-alpha * n) / (1 - eps) := by
    have : (2 : ℝ) ^ ((n : ℝ) * (hF - c * delta - alpha)) =
        (2 : ℝ) ^ (-alpha * n) * (2 : ℝ) ^ ((n : ℝ) * (hF - c * delta)) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    rw [this]
    have : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * (hF - c * delta)) := by positivity
    have : (1 - eps) ≠ 0 := by linarith
    field_simp
  have s5 : (2 : ℝ) ^ (-alpha * n) / (1 - eps) ≤ (2 : ℝ) ^ (-alpha * n + 1) / (1 - eps) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  linarith



end

