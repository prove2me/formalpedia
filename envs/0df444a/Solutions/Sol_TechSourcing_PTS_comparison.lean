-- Prove2me | solution 1 for TechSourcing.PTS.comparison
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T03:35:30.190857+00:00
-- url     : https://prove2.me/submissions/6156c533-11d3-4248-bcec-d2c570518c91

import Mathlib
import Definitions.Def_TechSourcing_PTS_Model
import Theorems.Thm_TechSourcing_PTS_thetaLStar_rewrite

open TechSourcing.PTS

private lemma cmp_id (a b L W s : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hs2 : s ^ 2 = 9 * a ^ 2 + 10 * a * b + b ^ 2) :
    (3/a+3/b+s/(a*b) - L - (1/a+3/b) + 1/2*L)^2 - ((1/a+3/b - 1/2*L)^2 + 6/a*(W-L)) =
      -(6/a)*(W - (1/3+2/3*((3*(a+b)-s)/(4*b)))*L - 2/3*(s/(a*b)) - 2/(3*a) - 2/(3*b)) := by
  have ha' := ha.ne'
  have hb' := hb.ne'
  field_simp
  linear_combination 48 * hs2

theorem solution (P : Params) (hP : P.Standing) (hWL : Lb P < Wb P)
    (hE0 : 0 < thetaEStar P) (hE1 : thetaEStar P < 1)
    (hL0 : 0 < thetaLStar P) (hL1 : thetaLStar P < 1) :
    (thetaLStar P ≤ thetaEStar P ↔ 0 ≤ Fcmp P) ∧
      (thetaLStar P < thetaEStar P ↔ 0 < Fcmp P) := by
  have hrw := thetaLStar_rewrite P hP hWL
  obtain ⟨ha, hb, hc, hD, hR, hβ0, hβ1⟩ := hP
  have hK : 0 < Wb P - Lb P := by linarith
  have hs2 : TechSourcing.PTS.sq P ^ 2 = 9 * P.a ^ 2 + 10 * P.a * P.b + P.b ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ TechSourcing.PTS.sq P := Real.sqrt_nonneg _
  have ht : Real.sqrt (9 / P.b ^ 2 + 10 / (P.a * P.b) + 1 / P.a ^ 2)
      = TechSourcing.PTS.sq P / (P.a * P.b) := by
    rw [show 9 / P.b ^ 2 + 10 / (P.a * P.b) + 1 / P.a ^ 2
        = (TechSourcing.PTS.sq P / (P.a * P.b)) ^ 2 by
      rw [div_pow, hs2]; field_simp]
    exact Real.sqrt_sq (by positivity)
  have hF : Fcmp P = Wb P - (1/3+2/3*((3*(P.a+P.b)-TechSourcing.PTS.sq P)/(4*P.b)))*Lb P
      - 2/3*(TechSourcing.PTS.sq P/(P.a*P.b)) - 2/(3*P.a) - 2/(3*P.b) := by
    unfold Fcmp gammaHat; rw [ht]
  have hden : denE P = 3/P.a+3/P.b+TechSourcing.PTS.sq P/(P.a*P.b) := rfl
  have hid := cmp_id P.a P.b (Lb P) (Wb P) (TechSourcing.PTS.sq P) ha hb hs2
  rw [← hden, ← hF] at hid
  set Z := (1 / P.a + 3 / P.b - 1 / 2 * Lb P) ^ 2 + 6 / P.a * (Wb P - Lb P) with hZ
  set dE := denE P - Lb P with hdE
  set dL := Real.sqrt Z + 1 / P.a + 3 / P.b - 1 / 2 * Lb P with hdL
  have hthE : thetaEStar P = (Wb P - Lb P) / dE := rfl
  have hthL : thetaLStar P = (Wb P - Lb P) / dL := hrw
  have hdEpos : 0 < dE := by
    rw [hthE] at hE0; exact (div_pos_iff_of_pos_left hK).1 hE0
  have hdLpos : 0 < dL := by
    rw [hthL] at hL0; exact (div_pos_iff_of_pos_left hK).1 hL0
  set Y := dE - (1 / P.a + 3 / P.b) + 1 / 2 * Lb P with hY
  have hZ0 : 0 ≤ Z := by
    have : 0 ≤ 6 / P.a * (Wb P - Lb P) := by positivity
    positivity
  have hsZ : Real.sqrt Z ^ 2 = Z := Real.sq_sqrt hZ0
  have hsZ0 : 0 ≤ Real.sqrt Z := Real.sqrt_nonneg _
  have habsle : |1 / P.a + 3 / P.b - 1 / 2 * Lb P| ≤ Real.sqrt Z := by
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    have : 0 ≤ 6 / P.a * (Wb P - Lb P) := by positivity
    linarith
  have hYlow : -Real.sqrt Z < Y := by
    have := le_abs_self (1 / P.a + 3 / P.b - 1 / 2 * Lb P)
    simp only [Y]; linarith
  have e1 : thetaLStar P ≤ thetaEStar P ↔ Y ≤ Real.sqrt Z := by
    rw [hthE, hthL, div_le_div_iff_of_pos_left hK hdLpos hdEpos]
    simp only [Y, dL]; constructor <;> intro h <;> linarith
  have e2 : thetaLStar P < thetaEStar P ↔ Y < Real.sqrt Z := by
    rw [hthE, hthL, div_lt_div_iff_of_pos_left hK hdLpos hdEpos]
    simp only [Y, dL]; constructor <;> intro h <;> linarith
  have h6 : 0 < 6 / P.a := by positivity
  rw [e1, e2]
  constructor
  · constructor
    · intro h
      have : Y ^ 2 ≤ Z := by rw [← hsZ]; exact sq_le_sq' hYlow.le h
      by_contra hc'; push Not at hc'
      have := mul_neg_of_pos_of_neg h6 hc'
      linarith
    · intro h
      have := mul_nonneg h6.le h
      have : Y ^ 2 ≤ Z := by linarith
      exact le_trans (le_abs_self Y) (Real.abs_le_sqrt this)
  · constructor
    · intro h
      have : Y ^ 2 < Z := by rw [← hsZ]; exact sq_lt_sq' hYlow h
      by_contra hc'; push Not at hc'
      have := mul_nonpos_of_nonneg_of_nonpos h6.le hc'
      linarith
    · intro h
      have := mul_pos h6 h
      have : Y ^ 2 < Z := by linarith
      by_contra hc'; push Not at hc'
      have : Real.sqrt Z ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hsZ0 hc' 2
      linarith
