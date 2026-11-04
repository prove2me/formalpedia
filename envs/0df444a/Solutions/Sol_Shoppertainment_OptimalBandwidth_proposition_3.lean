-- Prove2me | solution 1 for Shoppertainment.OptimalBandwidth.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T23:02:37.480003+00:00
-- url     : https://prove2.me/submissions/56c92614-b22b-4aed-b959-9eaf2982c7ff

import Mathlib
import Definitions.Def_Shoppertainment_OptimalBandwidth_Model
import Theorems.Thm_Shoppertainment_OptimalBandwidth_lemma_3
import Theorems.Thm_Shoppertainment_OptimalBandwidth_eq_14


namespace ShopP3Poly

noncomputable def g (a q : ℝ) : ℝ := (1 - q) * (q ^ 2 - a ^ 2) / (2 * (1 - a))
noncomputable def gp (a q : ℝ) : ℝ := (a ^ 2 + 2 * q - 3 * q ^ 2) / (2 * (1 - a))
noncomputable def Af (a q : ℝ) : ℝ := (5 - 3 * a ^ 2 - 3 * q + q ^ 3) / 6
noncomputable def NT (w a q : ℝ) : ℝ := gp a q * (2 - q) + (w + g a q)
noncomputable def NP (w a q : ℝ) : ℝ :=
  (gp a q * Af a q + (w + g a q) * ((q ^ 2 - 1) / 2)) * (2 - q) + 2 * (w + g a q) * Af a q

lemma NT_clear (w a q : ℝ) (ha1 : a < 1) :
    NT w a q * (2 * (1 - a)) = 2 * (1 - a) * w + (a ^ 2 + 2 * q ^ 3 - 7 * q ^ 2 + 4 * q) := by
  have : (1 - a) ≠ 0 := by linarith
  simp only [NT, gp, g]; field_simp; ring

lemma NP_clear (w a q : ℝ) (ha1 : a < 1) :
    NP w a q * (12 * (1 - a)) = 2 * (1 - a) * (4 - 6 * a ^ 2 - q ^ 3 + 6 * q ^ 2 - 3 * q) * w +
      (-3*a^4*q - 2*a^2*q^4 + 6*a^2*q^3 + 12*a^2*q^2 - 16*a^2*q + 6*a^2 + 4*q^6 - 15*q^5
        + 4*q^4 + 32*q^3 - 48*q^2 + 20*q) := by
  have : (1 - a) ≠ 0 := by linarith
  simp only [NP, gp, g, Af]; field_simp; ring

noncomputable def Dfun (q x : ℝ) : ℝ := -3 * q * x ^ 2 + x * (-2 * q ^ 4 + 6 * q ^ 3 + 12 * q ^ 2 - 16 * q + 6) +
        (4 * q ^ 6 - 15 * q ^ 5 + 4 * q ^ 4 + 32 * q ^ 3 - 48 * q ^ 2 + 20 * q)

lemma S_nonneg (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : 0 ≤ 2 * q ^ 3 - q ^ 2 / 2 - 15 * q / 4 + 31 / 8 := by
  have h : 2 * q ^ 3 - q ^ 2 / 2 - 15 * q / 4 + 31 / 8 = 2 * q * (q - 1/8) ^ 2 + (124 - 121 * q) / 32 := by ring
  rw [h]; have : 0 ≤ 2 * q * (q - 1/8) ^ 2 := by positivity
  linarith

lemma q_small (q : ℝ) (hq1 : q ≤ 1) (h : 0 ≤ 2 * q ^ 2 - 7 * q + 4) : q < 36 / 47 := by
  by_contra hc; push Not at hc
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hq1)]

lemma D0_pos (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (h : 0 ≤ 2 * q ^ 2 - 7 * q + 4) : 0 < Dfun q 0 := by
  have hS := S_nonneg q hq0.le hq1.le
  have hqs := q_small q hq1.le h
  have e : Dfun q 0 = q * ((2 * q ^ 2 - 7 * q + 4) * (2 * q ^ 3 - q ^ 2 / 2 - 15 * q / 4 + 31 / 8)
      + (9 / 2 - 47 * q / 8)) := by simp only [Dfun]; ring
  rw [e]
  have h1 := mul_nonneg h hS
  have : 0 < (2 * q ^ 2 - 7 * q + 4) * (2 * q ^ 3 - q ^ 2 / 2 - 15 * q / 4 + 31 / 8)
      + (9 / 2 - 47 * q / 8) := by linarith
  positivity

lemma Dq2_pos (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) : 0 < Dfun q (q ^ 2) := by
  have e : Dfun q (q ^ 2) = 2 * q * (2 - q) * (1 - q) ^ 2 * (5 + 2 * q - q ^ 2) := by
    simp only [Dfun]; ring
  rw [e]
  have : 0 < 2 - q := by linarith
  have : 0 < 1 - q := by linarith
  have : 0 < 5 + 2 * q - q ^ 2 := by nlinarith
  positivity

lemma Dβ_nonneg (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (h : 2 * q ^ 2 - 7 * q + 4 < 0) :
    0 ≤ Dfun q (-2 * q ^ 3 + 7 * q ^ 2 - 4 * q) := by
  have e : Dfun q (-2 * q ^ 3 + 7 * q ^ 2 - 4 * q) =
      2 * q * (2 - q) * (1 - q) ^ 3 * (-(4 * q ^ 2 - 11 * q + 1)) := by
    simp only [Dfun]; ring
  rw [e]
  have : 0 < 2 - q := by linarith
  have : 0 < 1 - q := by linarith
  have : 0 < -(4 * q ^ 2 - 11 * q + 1) := by nlinarith
  positivity

lemma D_chord (q b b0 : ℝ) : (q ^ 2 - b0) * Dfun q b =
    3 * q * (b - b0) * (q ^ 2 - b) * (q ^ 2 - b0) + (q ^ 2 - b) * Dfun q b0 + (b - b0) * Dfun q (q ^ 2) := by
  simp only [Dfun]; ring

lemma D_pos (q b : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hb0 : 0 ≤ b) (hbq : b < q ^ 2)
    (hβ : -2 * q ^ 3 + 7 * q ^ 2 - 4 * q < b) : 0 < Dfun q b := by
  have hDq2 := Dq2_pos q hq0 hq1
  rcases le_or_gt (-2 * q ^ 3 + 7 * q ^ 2 - 4 * q) 0 with hβ0 | hβ0
  · have hq2 : 0 ≤ 2 * q ^ 2 - 7 * q + 4 := by
      by_contra hc; push Not at hc
      have : 0 < q * (-(2 * q ^ 2 - 7 * q + 4)) := mul_pos hq0 (by linarith)
      nlinarith
    have hD0 := D0_pos q hq0 hq1 hq2
    have hc := D_chord q b 0
    have hq2pos : 0 < q ^ 2 - 0 := by rw [sub_zero]; positivity
    have t1 : 0 ≤ 3 * q * (b - 0) * (q ^ 2 - b) * (q ^ 2 - 0) := by
      have : 0 ≤ q ^ 2 - b := by linarith
      have : 0 ≤ b - 0 := by linarith
      positivity
    have t2 : 0 < (q ^ 2 - b) * Dfun q 0 := mul_pos (by linarith) hD0
    have t3 : 0 ≤ (b - 0) * Dfun q (q ^ 2) := mul_nonneg (by linarith) hDq2.le
    have : 0 < (q ^ 2 - 0) * Dfun q b := by rw [hc]; linarith
    exact pos_of_mul_pos_right this hq2pos.le
  · have hq2 : 2 * q ^ 2 - 7 * q + 4 < 0 := by
      by_contra hc; push Not at hc
      have : 0 ≤ q * (2 * q ^ 2 - 7 * q + 4) := mul_nonneg hq0.le hc
      nlinarith
    have hDβ := Dβ_nonneg q hq0 hq1 hq2
    have hc := D_chord q b (-2 * q ^ 3 + 7 * q ^ 2 - 4 * q)
    have hβq : 0 < q ^ 2 - (-2 * q ^ 3 + 7 * q ^ 2 - 4 * q) := by linarith
    have t1 : 0 ≤ 3 * q * (b - (-2 * q ^ 3 + 7 * q ^ 2 - 4 * q)) * (q ^ 2 - b) *
        (q ^ 2 - (-2 * q ^ 3 + 7 * q ^ 2 - 4 * q)) := by
      have : 0 ≤ q ^ 2 - b := by linarith
      have : 0 ≤ b - (-2 * q ^ 3 + 7 * q ^ 2 - 4 * q) := by linarith
      positivity
    have t2 : 0 ≤ (q ^ 2 - b) * Dfun q (-2 * q ^ 3 + 7 * q ^ 2 - 4 * q) := mul_nonneg (by linarith) hDβ
    have t3 : 0 < (b - (-2 * q ^ 3 + 7 * q ^ 2 - 4 * q)) * Dfun q (q ^ 2) := mul_pos (by linarith) hDq2
    have : 0 < (q ^ 2 - (-2 * q ^ 3 + 7 * q ^ 2 - 4 * q)) * Dfun q b := by rw [hc]; linarith
    exact pos_of_mul_pos_right this hβq.le

lemma claimA (w a q : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (haq : a < q) (hq1 : q < 1) (hw : 0 ≤ w)
    (hNT : 0 ≤ NT w a q) : 0 < NP w a q := by
  have he : 0 < 1 - a := by linarith
  have hq0 : 0 < q := by linarith
  have h1 := NT_clear w a q ha1
  have h2 := NP_clear w a q ha1
  have hc6 : 0 ≤ 4 - 6 * a ^ 2 - q ^ 3 + 6 * q ^ 2 - 3 * q := by
    have : a ^ 2 ≤ q ^ 2 := by nlinarith
    nlinarith [mul_pos hq0 hq0, mul_pos (mul_pos hq0 hq0) hq0]
  set Pp := a ^ 2 + 2 * q ^ 3 - 7 * q ^ 2 + 4 * q with hPp
  set Dd := (-3*a^4*q - 2*a^2*q^4 + 6*a^2*q^3 + 12*a^2*q^2 - 16*a^2*q + 6*a^2 + 4*q^6 - 15*q^5
        + 4*q^4 + 32*q^3 - 48*q^2 + 20*q) with hDd
  suffices h : 0 < NP w a q * (12 * (1 - a)) by
    exact pos_of_mul_pos_left h (by linarith)
  have hwP : 0 ≤ 2 * (1 - a) * w + Pp := by
    rw [← h1]; positivity
  rcases le_or_gt Pp 0 with hP | hP
  · -- binding constraint is NT ≥ 0
    have hX : 0 < 3 * q ^ 2 - 2 * q - a ^ 2 := by
      have : 3 * q ^ 2 - 2 * q - a ^ 2 = 2 * q * (1 - q) ^ 2 - Pp := by rw [hPp]; ring
      rw [this]; have : 0 < 2 * q * (1 - q) ^ 2 := by
        have : 0 < 1 - q := by linarith
        positivity
      linarith
    have hq2 : 2 * q ^ 2 - 7 * q + 4 ≤ 0 := by
      have : a ^ 2 + q * (2 * q ^ 2 - 7 * q + 4) ≤ 0 := by nlinarith
      by_contra hc; push Not at hc
      have := mul_pos hq0 hc; nlinarith [sq_nonneg a]
    have hY : 0 < -(3 * a ^ 2 + 2 * q ^ 3 - 6 * q ^ 2 + 1) := by
      have : -(3 * a ^ 2 + 2 * q ^ 3 - 6 * q ^ 2 + 1) = -3 * Pp + (1 - q) * (-4 * q ^ 2 + 11 * q - 1) := by
        rw [hPp]; ring
      rw [this]
      have : 0 < (1 - q) * (-4 * q ^ 2 + 11 * q - 1) := by
        apply mul_pos <;> nlinarith
      linarith
    have hid : (4 - 6 * a ^ 2 - q ^ 3 + 6 * q ^ 2 - 3 * q) * (-Pp) + Dd =
        (2 - q) * (3 * q ^ 2 - 2 * q - a ^ 2) * (-(3 * a ^ 2 + 2 * q ^ 3 - 6 * q ^ 2 + 1)) := by
      rw [hPp, hDd]; ring
    have hpos : 0 < (2 - q) * (3 * q ^ 2 - 2 * q - a ^ 2) * (-(3 * a ^ 2 + 2 * q ^ 3 - 6 * q ^ 2 + 1)) := by
      have : 0 < 2 - q := by linarith
      positivity
    rw [h2]
    have : (4 - 6 * a ^ 2 - q ^ 3 + 6 * q ^ 2 - 3 * q) * (-Pp) ≤
        (4 - 6 * a ^ 2 - q ^ 3 + 6 * q ^ 2 - 3 * q) * (2 * (1 - a) * w) :=
      mul_le_mul_of_nonneg_left (by linarith) hc6
    nlinarith
  · -- binding constraint is w ≥ 0: show Dd > 0
    have hw' : 0 ≤ 2 * (1 - a) * (4 - 6 * a ^ 2 - q ^ 3 + 6 * q ^ 2 - 3 * q) * w := by positivity
    rw [h2]
    suffices hD : 0 < Dd by linarith
    have hbq : a ^ 2 < q ^ 2 := by nlinarith
    have e : Dd = Dfun q (a ^ 2) := by rw [hDd]; simp only [Dfun]; ring
    rw [e]; exact D_pos q (a ^ 2) hq0 hq1 (sq_nonneg a) hbq (by rw [hPp] at hP; linarith)

lemma claimB (w a q0 q : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hw : 0 ≤ w) (haq0 : a ≤ q0) (hq0q : q0 ≤ q)
    (hq1 : q ≤ 1) (hN : NT w a q0 < 0) : NT w a q < 0 := by
  have he : 0 < 2 * (1 - a) := by linarith
  have e0 := NT_clear w a q0 ha1
  have e1 := NT_clear w a q ha1
  have ea := NT_clear w a a ha1
  have hNa : 0 ≤ NT w a a * (2 * (1 - a)) := by
    rw [ea]; have : 0 ≤ 2 * (1 - a) * w := by positivity
    nlinarith [mul_nonneg (mul_nonneg ha (by linarith : (0:ℝ) ≤ 1 - a)) (by linarith : (0:ℝ) ≤ 2 - a)]
  have hN0 : NT w a q0 * (2 * (1 - a)) < 0 := mul_neg_of_neg_of_pos hN he
  by_contra hc; push Not at hc
  have hN1 : 0 ≤ NT w a q * (2 * (1 - a)) := mul_nonneg hc he.le
  have chord : (q - a) * (NT w a q0 * (2 * (1 - a))) = (q - q0) * (NT w a a * (2 * (1 - a))) +
      (q0 - a) * (NT w a q * (2 * (1 - a))) + (q - a) * (q0 - a) * (q - q0) * (7 - 2 * (a + q0 + q)) := by
    rw [e0, e1, ea]; ring
  have hqa : a < q0 := by
    by_contra h'; push Not at h'
    have : q0 = a := le_antisymm h' haq0
    rw [this] at hN0; linarith
  have t1 : 0 ≤ (q - q0) * (NT w a a * (2 * (1 - a))) := mul_nonneg (by linarith) hNa
  have t2 : 0 ≤ (q0 - a) * (NT w a q * (2 * (1 - a))) := mul_nonneg (by linarith) hN1
  have t3 : 0 ≤ (q - a) * (q0 - a) * (q - q0) * (7 - 2 * (a + q0 + q)) := by
    have : 0 ≤ q - a := by linarith
    have : 0 ≤ q0 - a := by linarith
    have : 0 ≤ q - q0 := by linarith
    have : 0 ≤ 7 - 2 * (a + q0 + q) := by linarith
    positivity
  have : (q - a) * (NT w a q0 * (2 * (1 - a))) < 0 := mul_neg_of_pos_of_neg (by linarith) hN0
  linarith

lemma Af_pos (a q : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (haq : a ≤ q) (hq1 : q ≤ 1) : 0 < Af a q := by
  unfold Af
  have e : 5 - 3 * a ^ 2 - 3 * q + q ^ 3 = 3 * (q - a) * (q + a) + (1 - q) * (5 + 2 * q - q ^ 2) := by ring
  rw [e]
  rcases lt_or_eq_of_le haq with h | h
  · have : 0 < 3 * (q - a) * (q + a) := by
      have : 0 < q - a := by linarith
      have : 0 < q + a := by linarith
      positivity
    have : 0 ≤ (1 - q) * (5 + 2 * q - q ^ 2) := mul_nonneg (by linarith) (by nlinarith)
    linarith
  · subst h
    have : 0 < (1 - a) * (5 + 2 * a - a ^ 2) := mul_pos (by linarith) (by nlinarith)
    nlinarith

lemma g_nonneg (a q : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (haq : a ≤ q) (hq1 : q ≤ 1) : 0 ≤ g a q := by
  unfold g
  have : 0 ≤ q ^ 2 - a ^ 2 := by nlinarith
  have : 0 ≤ 1 - q := by linarith
  have : 0 < 2 * (1 - a) := by linarith
  positivity

lemma g_pos (a q : ℝ) (ha : 0 ≤ a) (haq : a < q) (hq1 : q < 1) : 0 < g a q := by
  unfold g
  have : 0 < q ^ 2 - a ^ 2 := by nlinarith
  have : 0 < 1 - q := by linarith
  have : 0 < 2 * (1 - a) := by linarith
  positivity

/-- Part 4 polynomial inequality. -/
lemma part4_poly (w a q : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (haq : a < q) (hq1 : q < 1)
    (hw : (1 + a) / 4 < w) : (w + g a q) * Af a q / (2 - q) ^ 2 < w * ((1 - a ^ 2) / 2) := by
  have h2q : 0 < (2 - q) ^ 2 := by nlinarith
  rw [div_lt_iff₀ h2q]
  have he : 0 < 1 - a := by linarith
  have hq0 : 0 < q := by linarith
  -- B > 0
  have hB : 0 < 3 * a ^ 2 * q - 9 * a ^ 2 + q ^ 2 - 2 * q + 7 := by
    have h1 : 3 * a ^ 2 * q - 9 * a ^ 2 + q ^ 2 - 2 * q + 7 =
        3 * (q ^ 2 - a ^ 2) * (3 - q) + (1 - q) * (7 + 5 * q - 3 * q ^ 2) := by ring
    have : 0 < q ^ 2 - a ^ 2 := by nlinarith
    have : 0 < 3 * (q ^ 2 - a ^ 2) * (3 - q) := by
      have : 0 < 3 - q := by linarith
      positivity
    have : 0 ≤ (1 - q) * (7 + 5 * q - 3 * q ^ 2) := mul_nonneg (by linarith) (by nlinarith)
    linarith
  -- H > 0
  have hH : 0 < 3*a^4 - 2*a^2*q^2 - 7*a^2*q - 6*a^2 + 2*q^4 + 2*q^3 - 4*q^2 + 5*q + 7 := by
    have h1 : 3*a^4 - 2*a^2*q^2 - 7*a^2*q - 6*a^2 + 2*q^4 + 2*q^3 - 4*q^2 + 5*q + 7 =
        (q ^ 2 - a ^ 2) * (6 + 7 * q - q ^ 2 - 3 * a ^ 2) + (1 - q) * (7 + 12 * q + 2 * q ^ 2 - 3 * q ^ 3) := by
      ring
    have : 0 < q ^ 2 - a ^ 2 := by nlinarith
    have : 0 < 6 + 7 * q - q ^ 2 - 3 * a ^ 2 := by nlinarith
    have : 0 < (q ^ 2 - a ^ 2) * (6 + 7 * q - q ^ 2 - 3 * a ^ 2) := by positivity
    have : 0 ≤ (1 - q) * (7 + 12 * q + 2 * q ^ 2 - 3 * q ^ 3) := mul_nonneg (by linarith) (by nlinarith)
    linarith
  have key : (w * ((1 - a ^ 2) / 2) * (2 - q) ^ 2 - (w + g a q) * Af a q) * (2 * (1 - a)) =
      2 * (1 - a) * (w - (1 + a) / 4) * ((1 - q) * (3 * a ^ 2 * q - 9 * a ^ 2 + q ^ 2 - 2 * q + 7) / 6) +
      (q - 1) ^ 2 * (3*a^4 - 2*a^2*q^2 - 7*a^2*q - 6*a^2 + 2*q^4 + 2*q^3 - 4*q^2 + 5*q + 7) / 12 := by
    have : (1 - a) ≠ 0 := by linarith
    simp only [g, Af]; field_simp; ring
  have t1 : 0 < 2 * (1 - a) * (w - (1 + a) / 4) * ((1 - q) * (3 * a ^ 2 * q - 9 * a ^ 2 + q ^ 2 - 2 * q + 7) / 6) := by
    have : 0 < w - (1 + a) / 4 := by linarith
    have : 0 < 1 - q := by linarith
    positivity
  have t2 : 0 ≤ (q - 1) ^ 2 * (3*a^4 - 2*a^2*q^2 - 7*a^2*q - 6*a^2 + 2*q^4 + 2*q^3 - 4*q^2 + 5*q + 7) / 12 := by
    positivity
  have : 0 < (w * ((1 - a ^ 2) / 2) * (2 - q) ^ 2 - (w + g a q) * Af a q) * (2 * (1 - a)) := by
    rw [key]; linarith
  have := pos_of_mul_pos_left this (by linarith)
  linarith

noncomputable def h1 (w a q : ℝ) : ℝ := (w + g a q) / (2 - q)
noncomputable def h2 (w a q : ℝ) : ℝ := (w + g a q) * Af a q / (2 - q) ^ 2

lemma hd_u (w a x : ℝ) (ha1 : a < 1) : HasDerivAt (fun q => w + g a q) (gp a x) x := by
  have h := ((((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).mul
    ((hasDerivAt_pow 2 x).sub (hasDerivAt_const x (a ^ 2)))).div_const (2 * (1 - a))).const_add w
  have e : ((0 - 1) * (x ^ 2 - a ^ 2) + (1 - id x) * (↑2 * x ^ (2 - 1) - 0)) / (2 * (1 - a)) = gp a x := by
    have : (1 - a) ≠ 0 := by linarith
    simp only [gp, id]; field_simp; ring
  exact h.congr_deriv e

lemma hd_A (a x : ℝ) : HasDerivAt (fun q => Af a q) ((x ^ 2 - 1) / 2) x := by
  have h := ((((hasDerivAt_const x (5 - 3 * a ^ 2 : ℝ)).sub ((hasDerivAt_id x).const_mul 3)).add
    (hasDerivAt_pow 3 x))).div_const 6
  have e : (0 - 3 * 1 + ↑3 * x ^ (3 - 1)) / 6 = (x ^ 2 - 1) / 2 := by norm_num; ring
  exact h.congr_deriv e

lemma hd_h1 (w a x : ℝ) (ha1 : a < 1) (hx : x < 2) :
    HasDerivAt (h1 w a) (NT w a x / (2 - x) ^ 2) x := by
  have hd : HasDerivAt (fun q : ℝ => 2 - q) (0 - 1) x := (hasDerivAt_const x (2:ℝ)).sub (hasDerivAt_id x)
  have h := (hd_u w a x ha1).div hd (by linarith)
  have e : (gp a x * (2 - x) - (w + g a x) * (0 - 1)) / (2 - x) ^ 2 = NT w a x / (2 - x) ^ 2 := by
    simp only [NT]; ring
  exact h.congr_deriv e

lemma hd_h2 (w a x : ℝ) (ha1 : a < 1) (hx : x < 2) :
    HasDerivAt (h2 w a) (NP w a x / (2 - x) ^ 3) x := by
  have hd : HasDerivAt (fun q : ℝ => (2 - q) ^ 2) (↑2 * (2 - x) ^ (2 - 1) * (0 - 1)) x :=
    ((hasDerivAt_const x (2:ℝ)).sub (hasDerivAt_id x)).pow 2
  have hne : (2 - x) ^ 2 ≠ 0 := by have : (2 - x) ≠ 0 := by linarith
                                   positivity
  have h := ((hd_u w a x ha1).mul (hd_A a x)).div hd hne
  have e : ((gp a x * Af a x + (w + g a x) * ((x ^ 2 - 1) / 2)) * (2 - x) ^ 2 -
      (w + g a x) * Af a x * (↑2 * (2 - x) ^ (2 - 1) * (0 - 1))) / ((2 - x) ^ 2) ^ 2 =
      NP w a x / (2 - x) ^ 3 := by
    have : (2 - x) ≠ 0 := by linarith
    simp only [NP]; field_simp; ring
  exact h.congr_deriv e

end ShopP3Poly

namespace ShopP3Aux
open Shoppertainment.OptimalBandwidth ShopP3Poly

lemma int_quad (c1 c2 x y : ℝ) :
    ∫ q in x..y, (c1 * q + c2 * q ^ 2) = c1 * ((y ^ 2 - x ^ 2) / 2) + c2 * ((y ^ 3 - x ^ 3) / 3) := by
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_id, integral_pow]
  · norm_num
  · exact (continuous_const.mul continuous_id).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _

lemma eup_int (v a t Q : ℝ) :
    ∫ q in a..Q, (1 - t) * q * v = (1 - t) * v * ((Q ^ 2 - a ^ 2) / 2) := by
  have := int_quad ((1 - t) * v) 0 a Q
  simp only [zero_mul, add_zero] at this
  rw [← this]; congr 1; funext q; ring

lemma pL_int (v a t Q : ℝ) :
    ∫ q in a..Q, pL v t q = t * v * ((Q ^ 2 - a ^ 2) / 2) := by
  have := int_quad (t * v) 0 a Q
  simp only [zero_mul, add_zero] at this
  rw [← this]; congr 1; funext q; simp only [pL]; ring

lemma pH_int (v a t Q : ℝ) :
    ∫ q in a..Q, pH v t q * q = (1 - t) * v * ((Q ^ 2 - a ^ 2) / 2) + t * v * ((Q ^ 3 - a ^ 3) / 3) := by
  rw [← int_quad]; congr 1; funext q; simp only [pH]; ring

/-- closed form, region 1 -/
lemma payoff_r1 (α v ve K a : ℝ) (hα : 0 < α) (hα1 : α < 1) (hv : 0 < v)
    (ha : 0 ≤ a) (ha1 : a < 1) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (hth : t ≤ teHat a) :
    payoff α v ve K a t = ve * t / K * (α * v / (1 - a) *
      ((1 - t) * ((1 - a ^ 2) / 2) + t * ((1 - a ^ 3) / 3))) := by
  have h3 := lemma_3 v a hv ha ha1 t ht
  have h14 := eq_14 α v a hα hα1 hv ha ha1 t ht
  have hn : ¬ teHat a < t := not_lt.mpr hth
  rw [if_neg hn] at h3 h14
  simp only [payoff, traffic, profitability] at *
  rw [h14, h3, pH_int]
  ring

/-- closed form, region 2 -/
lemma payoff_r2 (α v ve K a : ℝ) (hα : 0 < α) (hα1 : α < 1) (hv : 0 < v)
    (ha : 0 ≤ a) (ha1 : a < 1) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (hth : teHat a < t) :
    payoff α v ve K a t = (ve * t + v / (1 - a) * ((1 - t) * ((qHat t ^ 2 - a ^ 2) / 2))) / K *
      (α * v / (1 - a) * (t * ((qHat t ^ 2 - a ^ 2) / 2) +
        ((1 - t) * ((1 - qHat t ^ 2) / 2) + t * ((1 - qHat t ^ 3) / 3)))) := by
  have h3 := lemma_3 v a hv ha ha1 t ht
  have h14 := eq_14 α v a hα hα1 hv ha ha1 t ht
  rw [if_pos hth] at h3 h14
  simp only [payoff, traffic, profitability] at *
  rw [h14, h3, pH_int, pL_int, eup_int]
  ring

lemma traffic_r1 (v ve K a : ℝ) (hv : 0 < v)
    (ha : 0 ≤ a) (ha1 : a < 1) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (hth : t ≤ teHat a) :
    traffic v ve K a t = ve * t / K := by
  have h3 := lemma_3 v a hv ha ha1 t ht
  rw [if_neg (not_lt.mpr hth)] at h3
  simp only [traffic, h3, add_zero]

lemma traffic_r2 (v ve K a : ℝ) (hv : 0 < v)
    (ha : 0 ≤ a) (ha1 : a < 1) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (hth : teHat a < t) :
    traffic v ve K a t = (ve * t + v / (1 - a) * ((1 - t) * ((qHat t ^ 2 - a ^ 2) / 2))) / K := by
  have h3 := lemma_3 v a hv ha ha1 t ht
  rw [if_pos hth] at h3
  simp only [traffic, h3, eup_int]
  ring

lemma teHat_eq (a : ℝ) : teHat a = 1 / (2 - a) := rfl

lemma tq_mem (a q : ℝ) (ha : 0 ≤ a) (haq : a ≤ q) (hq1 : q ≤ 1) : 1 / (2 - q) ∈ Set.Icc (0:ℝ) 1 := by
  have h2 : 0 < 2 - q := by linarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_one h2]; linarith

lemma th_lt_tq (a q : ℝ) (ha1 : a < 1) (haq : a < q) (hq1 : q ≤ 1) : teHat a < 1 / (2 - q) := by
  rw [teHat_eq]; apply one_div_lt_one_div_of_lt <;> linarith

lemma qHat_tq (q : ℝ) : qHat (1 / (2 - q)) = q := by
  simp [qHat]

lemma tq_qHat (t : ℝ) (ht : 0 < t) : 1 / (2 - qHat t) = t := by
  simp [qHat]

lemma payoff_q (α v ve K a : ℝ) (hα : 0 < α) (hα1 : α < 1) (hv : 0 < v) (hK : 0 < K)
    (ha : 0 ≤ a) (ha1 : a < 1) (q : ℝ) (haq : a ≤ q) (hq1 : q ≤ 1) :
    payoff α v ve K a (1 / (2 - q)) = α * v ^ 2 / (K * (1 - a)) * h2 (ve / v) a q := by
  have hmem := tq_mem a q ha haq hq1
  have h2q : (2 - q) ≠ 0 := by linarith
  have h1a : (1 - a) ≠ 0 := by linarith
  have hv0 : v ≠ 0 := hv.ne'
  have hK0 : K ≠ 0 := hK.ne'
  rcases lt_or_eq_of_le haq with h | h
  · rw [payoff_r2 α v ve K a hα hα1 hv ha ha1 _ hmem (th_lt_tq a q ha1 h hq1), qHat_tq]
    simp only [h2, g, Af]
    field_simp; ring
  · subst h
    rw [payoff_r1 α v ve K a hα hα1 hv ha ha1 _ hmem (le_of_eq (teHat_eq a).symm)]
    simp only [h2, g, Af]
    have h2a : (2 - a) ≠ 0 := by linarith
    field_simp; ring

lemma traffic_q (v ve K a : ℝ) (hv : 0 < v) (hK : 0 < K)
    (ha : 0 ≤ a) (ha1 : a < 1) (q : ℝ) (haq : a ≤ q) (hq1 : q ≤ 1) :
    traffic v ve K a (1 / (2 - q)) = v / K * h1 (ve / v) a q := by
  have hmem := tq_mem a q ha haq hq1
  have h2q : (2 - q) ≠ 0 := by linarith
  have h1a : (1 - a) ≠ 0 := by linarith
  have hv0 : v ≠ 0 := hv.ne'
  have hK0 : K ≠ 0 := hK.ne'
  rcases lt_or_eq_of_le haq with h | h
  · rw [traffic_r2 v ve K a hv ha ha1 _ hmem (th_lt_tq a q ha1 h hq1), qHat_tq]
    simp only [h1, g]
    field_simp; ring
  · subst h
    rw [traffic_r1 v ve K a hv ha ha1 _ hmem (le_of_eq (teHat_eq a).symm)]
    simp only [h1, g]
    field_simp; ring

noncomputable def r1 (a t : ℝ) : ℝ := t * ((1 - t) * ((1 - a ^ 2) / 2) + t * ((1 - a ^ 3) / 3))

lemma payoff_r1' (α v ve K a : ℝ) (hα : 0 < α) (hα1 : α < 1) (hv : 0 < v)
    (ha : 0 ≤ a) (ha1 : a < 1) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (hth : t ≤ teHat a) :
    payoff α v ve K a t = ve * (α * v / (K * (1 - a))) * r1 a t := by
  rw [payoff_r1 α v ve K a hα hα1 hv ha ha1 t ht hth, r1]
  have h1a : (1 - a) ≠ 0 := by linarith
  rcases eq_or_ne K 0 with hK | hK
  · subst hK; simp
  · field_simp

lemma r1_lt (a s t : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    r1 a s < r1 a t := by
  have e : r1 a t - r1 a s = (t - s) * ((1 - a ^ 2) / 2 - (s + t) * ((1 - a) * (1 - a) * (1 + 2 * a) / 6)) := by
    simp only [r1]; ring
  have hc : 0 ≤ (1 - a) * (1 - a) * (1 + 2 * a) / 6 := by
    have : 0 ≤ 1 - a := by linarith
    positivity
  have hb : 0 < (1 - a ^ 2) / 2 - (s + t) * ((1 - a) * (1 - a) * (1 + 2 * a) / 6) := by
    have h1 : (s + t) * ((1 - a) * (1 - a) * (1 + 2 * a) / 6) ≤ 2 * ((1 - a) * (1 - a) * (1 + 2 * a) / 6) :=
      mul_le_mul_of_nonneg_right (by linarith) hc
    have h2 : (1 - a ^ 2) / 2 - 2 * ((1 - a) * (1 - a) * (1 + 2 * a) / 6) = (1 - a) * (1 + a + 4 * a ^ 2) / 6 := by
      ring
    have h3 : 0 < (1 - a) * (1 + a + 4 * a ^ 2) / 6 := by
      have : 0 < 1 - a := by linarith
      positivity
    linarith
  have : 0 < r1 a t - r1 a s := by rw [e]; exact mul_pos (by linarith) hb
  linarith

lemma r1_le (a s t : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    r1 a s ≤ r1 a t := by
  rcases lt_or_eq_of_le hst with h | h
  · exact (r1_lt a s t ha ha1 hs h ht).le
  · rw [h]

lemma r1_lt_end (a t : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (ht0 : 0 ≤ t) (ht : t < 1) :
    r1 a t < (1 - a ^ 2) / 2 := by
  have e : r1 a t = t * ((1 - a ^ 2) / 2 - t * ((1 - a) * (1 - a) * (1 + 2 * a) / 6)) := by
    simp only [r1]; ring
  have hc : 0 ≤ t * ((1 - a) * (1 - a) * (1 + 2 * a) / 6) := by
    have : 0 ≤ 1 - a := by linarith
    positivity
  have hp : 0 < 1 - a ^ 2 := by nlinarith
  rw [e]
  have : t * ((1 - a ^ 2) / 2 - t * ((1 - a) * (1 - a) * (1 + 2 * a) / 6)) ≤ t * ((1 - a ^ 2) / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) ht0
  nlinarith

end ShopP3Aux

open Shoppertainment.OptimalBandwidth ShopP3Poly ShopP3Aux in
theorem solution (α v ve K ql : ℝ) (hα : 0 < α) (hα1 : α < 1) (hv : 0 < v) (hK : 0 < K)
    (hql : 0 ≤ ql) (hql1 : ql < 1) (hve : 0 ≤ ve) :
    ¬ IsMaxOn (payoff α v ve K ql) (Set.Icc 0 1) 0 ∧
    (∃ t ∈ Set.Icc (0:ℝ) 1, IsMaxOn (payoff α v ve K ql) (Set.Icc 0 1) t) ∧
    (ve ≤ v * (1 + ql) / 4 →
      ∀ tS ∈ Set.Icc (0:ℝ) 1, IsMaxOn (payoff α v ve K ql) (Set.Icc 0 1) tS →
      ∀ tT ∈ Set.Icc (0:ℝ) 1, IsMaxOn (traffic v ve K ql) (Set.Icc 0 1) tT → tT ≤ tS) ∧
    (v * (1 + ql) / 4 < ve →
      ∀ t ∈ Set.Ico (0:ℝ) 1, payoff α v ve K ql t < payoff α v ve K ql 1) := by
  set a := ql with ha_def
  set w := ve / v with hw_def
  have hw0 : 0 ≤ w := div_nonneg hve hv.le
  set C := α * v ^ 2 / (K * (1 - a)) with hC_def
  have hC : 0 < C := by
    have : 0 < 1 - a := by linarith
    positivity
  set C1 := α * v / (K * (1 - a)) with hC1_def
  have hC1 : 0 < C1 := by
    have : 0 < 1 - a := by linarith
    positivity
  have hCw : C * w = ve * C1 := by
    rw [hC_def, hC1_def, hw_def]; field_simp
  set th := teHat a with hth_def
  have hth : th = 1 / (2 - a) := rfl
  have hth0 : 0 < th := by
    rw [hth]; have : 0 < 2 - a := by linarith
    positivity
  have hth1 : th < 1 := by rw [hth, div_lt_one (by linarith)]; linarith
  have hthm : th ∈ Set.Icc (0:ℝ) 1 := ⟨hth0.le, hth1.le⟩
  -- region-1 formula
  have R1 : ∀ t ∈ Set.Icc (0:ℝ) 1, t ≤ th → payoff α v ve K a t = ve * C1 * r1 a t :=
    fun t ht hle => payoff_r1' α v ve K a hα hα1 hv hql hql1 t ht hle
  -- q-formula
  have PQ : ∀ q, a ≤ q → q ≤ 1 → payoff α v ve K a (1 / (2 - q)) = C * h2 w a q :=
    fun q h1 h2 => payoff_q α v ve K a hα hα1 hv hK hql hql1 q h1 h2
  have TQ : ∀ q, a ≤ q → q ≤ 1 → traffic v ve K a (1 / (2 - q)) = v / K * h1 w a q :=
    fun q h1 h2 => traffic_q v ve K a hv hK hql hql1 q h1 h2
  -- payoff at th
  have Pth : payoff α v ve K a th = C * h2 w a a := by rw [hth]; exact PQ a le_rfl hql1.le
  -- region-1 monotone
  have R1le : ∀ t ∈ Set.Icc (0:ℝ) 1, t ≤ th → payoff α v ve K a t ≤ payoff α v ve K a th := by
    intro t ht hle
    rw [R1 t ht hle, R1 th hthm le_rfl]
    have : 0 ≤ ve * C1 := by positivity
    exact mul_le_mul_of_nonneg_left (r1_le a t th hql hql1 ht.1 hle hth1.le) this
  -- t ∈ (th, 1] ↦ q
  have Tq : ∀ t, th < t → t ≤ 1 → a < qHat t ∧ qHat t ≤ 1 ∧ 1 / (2 - qHat t) = t := by
    intro t h1 h2
    have ht0 : 0 < t := lt_trans hth0 h1
    refine ⟨?_, ?_, tq_qHat t ht0⟩
    · have : 1 / t < 2 - a := by
        rw [div_lt_iff₀ ht0]; rw [hth, div_lt_iff₀ (by linarith)] at h1; linarith
      simp only [qHat]; linarith
    · have : 1 ≤ 1 / t := by rw [le_div_iff₀ ht0]; linarith
      simp only [qHat]; linarith
  -- a positive point
  set qm := (1 + a) / 2 with hqm
  have hqm1 : a < qm := by rw [hqm]; linarith
  have hqm2 : qm < 1 := by rw [hqm]; linarith
  have Ppos : 0 < payoff α v ve K a (1 / (2 - qm)) := by
    rw [PQ qm hqm1.le hqm2.le]
    have hg := g_pos a qm hql hqm1 hqm2
    have hA := Af_pos a qm hql hql1 hqm1.le hqm2.le
    have : 0 < (2 - qm) ^ 2 := by nlinarith
    simp only [h2]
    have : 0 < w + g a qm := by linarith
    positivity
  have qmmem := tq_mem a qm hql hqm1.le hqm2.le
  have P0 : payoff α v ve K a 0 = 0 := by
    rw [R1 0 ⟨le_rfl, zero_le_one⟩ hth0.le]; simp [r1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- part 1
    intro hmax
    have := hmax qmmem
    simp only [Set.mem_setOf_eq] at this
    rw [P0] at this; linarith
  · -- part 2
    have hcont : ContinuousOn (payoff α v ve K a) (Set.Icc th 1) := by
      have hc : ContinuousOn (fun t => C * h2 w a (qHat t)) (Set.Icc th 1) := by
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le hth0 ht.1
        have hq1 : qHat t ≤ 1 := by
          have : 1 ≤ 1 / t := by rw [le_div_iff₀ ht0]; linarith [ht.2]
          simp only [qHat]; linarith
        have hqc : ContinuousAt qHat t := by
          unfold qHat
          exact continuousAt_const.sub (continuousAt_const.div continuousAt_id ht0.ne')
        have hh2 : ContinuousAt (h2 w a) (qHat t) :=
          (hd_h2 w a (qHat t) hql1 (by linarith)).continuousAt
        exact (continuousAt_const.mul (hh2.comp hqc)).continuousWithinAt
      refine hc.congr ?_
      intro t ht
      rcases lt_or_eq_of_le ht.1 with h | h
      · obtain ⟨hqa, hq1, hqt⟩ := Tq t h ht.2
        simp only
        conv_lhs => rw [← hqt]
        exact PQ _ hqa.le hq1
      · rw [← h, Pth]
        simp only
        have : qHat th = a := by
          rw [hth]; exact qHat_tq a
        rw [this]
    obtain ⟨ts, hts, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨th, le_rfl, hth1.le⟩ hcont
    refine ⟨ts, ⟨le_trans hth0.le hts.1, hts.2⟩, ?_⟩
    intro t ht
    simp only [Set.mem_setOf_eq]
    rcases le_or_gt t th with h | h
    · exact le_trans (R1le t ht h) (hmax ⟨le_rfl, hth1.le⟩)
    · exact hmax ⟨h.le, ht.2⟩
  · -- part 3
    intro _ tS htS hS tT htT hT
    by_contra hlt
    push Not at hlt
    have hposS : 0 < payoff α v ve K a tS := lt_of_lt_of_le Ppos (hS qmmem)
    rcases le_or_gt tT th with hTth | hTth
    · have hSth : tS ≤ th := by linarith
      have hve0 : 0 < ve := by
        rcases lt_or_eq_of_le hve with h | h
        · exact h
        · exfalso; rw [R1 tS htS hSth, ← h] at hposS; simp at hposS
      have hlt' : payoff α v ve K a tS < payoff α v ve K a tT := by
        rw [R1 tS htS hSth, R1 tT htT hTth]
        exact mul_lt_mul_of_pos_left (r1_lt a tS tT hql hql1 htS.1 hlt htT.2) (by positivity)
      have := hS htT
      simp only [Set.mem_setOf_eq] at this
      linarith
    · obtain ⟨hqTa, hqT1, hqTt⟩ := Tq tT hTth htT.2
      set qT := qHat tT with hqT
      -- NT ≥ 0 on (a, qT)
      have hNT : ∀ q ∈ Set.Ioo a qT, 0 ≤ NT w a q := by
        intro q hq
        by_contra hneg
        push Not at hneg
        have hanti : StrictAntiOn (h1 w a) (Set.Icc q 1) := by
          apply strictAntiOn_of_deriv_neg (convex_Icc q 1)
          · intro x hx
            exact (hd_h1 w a x hql1 (by linarith [hx.2])).continuousAt.continuousWithinAt
          · intro x hx
            rw [interior_Icc] at hx
            rw [(hd_h1 w a x hql1 (by linarith [hx.2])).deriv]
            have hN := claimB w a q x hql hql1 hw0 hq.1.le hx.1.le hx.2.le hneg
            have : 0 < (2 - x) ^ 2 := by nlinarith [hx.2]
            exact div_neg_of_neg_of_pos hN this
        have h1lt : h1 w a qT < h1 w a q :=
          hanti ⟨le_rfl, by linarith [hq.2]⟩ ⟨hq.2.le, hqT1⟩ hq.2
        have hTlt : traffic v ve K a tT < traffic v ve K a (1 / (2 - q)) := by
          rw [← hqTt, TQ qT hqTa.le hqT1, TQ q hq.1.le (by linarith [hq.2])]
          exact mul_lt_mul_of_pos_left h1lt (by positivity)
        have := hT (tq_mem a q hql hq.1.le (by linarith [hq.2]))
        simp only [Set.mem_setOf_eq] at this
        linarith
      have hmono : StrictMonoOn (h2 w a) (Set.Icc a qT) := by
        apply strictMonoOn_of_deriv_pos (convex_Icc a qT)
        · intro x hx
          exact (hd_h2 w a x hql1 (by linarith [hx.2])).continuousAt.continuousWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          rw [(hd_h2 w a x hql1 (by linarith [hx.2])).deriv]
          have hN := claimA w a x hql hql1 hx.1 (by linarith [hx.2]) hw0 (hNT x hx)
          have : 0 < (2 - x) ^ 3 := by
            have : 0 < 2 - x := by linarith [hx.2]
            positivity
          exact div_pos hN this
      have PT : payoff α v ve K a tT = C * h2 w a qT := by
        rw [← hqTt]; exact PQ qT hqTa.le hqT1
      have hlt' : payoff α v ve K a tS < payoff α v ve K a tT := by
        rcases le_or_gt tS th with hSth | hSth
        · have h1 := R1le tS htS hSth
          rw [Pth] at h1
          have h2' : h2 w a a < h2 w a qT := hmono ⟨le_rfl, hqTa.le⟩ ⟨hqTa.le, le_rfl⟩ hqTa
          rw [PT]
          have := mul_lt_mul_of_pos_left h2' hC
          linarith
        · obtain ⟨hqSa, hqS1, hqSt⟩ := Tq tS hSth htS.2
          have hqST : qHat tS < qT := by
            rw [hqT]; simp only [qHat]
            have h0 : 0 < tS := lt_trans hth0 hSth
            have : 1 / tT < 1 / tS := one_div_lt_one_div_of_lt h0 hlt
            linarith
          rw [PT, ← hqSt, PQ _ hqSa.le hqS1]
          exact mul_lt_mul_of_pos_left (hmono ⟨hqSa.le, hqST.le⟩ ⟨hqTa.le, le_rfl⟩ hqST) hC
      have := hS htT
      simp only [Set.mem_setOf_eq] at this
      linarith
  · -- part 4
    intro hbig t ht
    have hw : (1 + a) / 4 < w := by
      rw [hw_def, lt_div_iff₀ hv]; linarith
    have hve0 : 0 < ve := by
      have : 0 < v * (1 + a) / 4 := by positivity
      linarith
    have P1 : payoff α v ve K a 1 = C * (w * ((1 - a ^ 2) / 2)) := by
      have := PQ 1 hql1.le le_rfl
      have e1 : (1:ℝ) / (2 - 1) = 1 := by norm_num
      rw [e1] at this
      rw [this]; congr 1; simp only [h2, g, Af]; ring
    rw [P1]
    rcases le_or_gt t th with h | h
    · rw [R1 t ⟨ht.1, ht.2.le⟩ h, ← mul_assoc, hCw]
      exact mul_lt_mul_of_pos_left (r1_lt_end a t hql hql1 ht.1 ht.2) (by positivity)
    · obtain ⟨hqa, _, hqt⟩ := Tq t h ht.2.le
      have hq1 : qHat t < 1 := by
        have ht0 : 0 < t := lt_trans hth0 h
        have : 1 < 1 / t := by rw [lt_div_iff₀ ht0]; linarith [ht.2]
        simp only [qHat]; linarith
      rw [← hqt, PQ _ hqa.le hq1.le]
      exact mul_lt_mul_of_pos_left (part4_poly w a _ hql hql1 hqa hq1 hw) hC
