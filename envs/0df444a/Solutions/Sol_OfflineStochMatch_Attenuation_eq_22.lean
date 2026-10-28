-- Prove2me | solution 1 for OfflineStochMatch.Attenuation.eq_22
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T07:21:48.960285+00:00
-- url     : https://prove2.me/submissions/b41615fd-adfa-4d7d-a31c-b45724c934b8

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting

namespace OfflineStochMatch.Attenuation.Eq22Aux

open Real

/-- Antiderivative identity: `∫₀¹ e^{-4x} (4P - P')(x) dx = P(0) - e^{-4} P(1)` for a
quintic `P = b0 + b1 x + ... + b5 x^5`. -/
lemma integral_exp_poly (b0 b1 b2 b3 b4 b5 : ℝ) :
    ∫ x in (0 : ℝ)..1, Real.exp (-4 * x) *
      ((4 * b0 - b1) + (4 * b1 - 2 * b2) * x + (4 * b2 - 3 * b3) * x ^ 2 +
        (4 * b3 - 4 * b4) * x ^ 3 + (4 * b4 - 5 * b5) * x ^ 4 + 4 * b5 * x ^ 5)
      = b0 - Real.exp (-4) * (b0 + b1 + b2 + b3 + b4 + b5) := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun x => -Real.exp (-4 * x) *
        (b0 + b1 * x + b2 * x ^ 2 + b3 * x ^ 3 + b4 * x ^ 4 + b5 * x ^ 5))
        (Real.exp (-4 * x) *
          ((4 * b0 - b1) + (4 * b1 - 2 * b2) * x + (4 * b2 - 3 * b3) * x ^ 2 +
            (4 * b3 - 4 * b4) * x ^ 3 + (4 * b4 - 5 * b5) * x ^ 4 + 4 * b5 * x ^ 5)) x := by
    intro x _
    have h1 : HasDerivAt (fun x => Real.exp (-4 * x)) (Real.exp (-4 * x) * (-4)) x := by
      have := ((hasDerivAt_id x).const_mul (-4)).exp
      simpa using this
    have hp : HasDerivAt
        (fun x => b0 + b1 * x + b2 * x ^ 2 + b3 * x ^ 3 + b4 * x ^ 4 + b5 * x ^ 5)
        (b1 + 2 * b2 * x + 3 * b3 * x ^ 2 + 4 * b4 * x ^ 3 + 5 * b5 * x ^ 4) x := by
      have e1 := (hasDerivAt_id x).const_mul b1
      have e2 := (hasDerivAt_pow 2 x).const_mul b2
      have e3 := (hasDerivAt_pow 3 x).const_mul b3
      have e4 := (hasDerivAt_pow 4 x).const_mul b4
      have e5 := (hasDerivAt_pow 5 x).const_mul b5
      have := (((((hasDerivAt_const x b0).add e1).add e2).add e3).add e4).add e5
      exact this.congr_deriv (by norm_num <;> ring)
    have := h1.neg.mul hp
    exact this.congr_deriv (by simp only [Pi.neg_apply]; ring)
  have hint : IntervalIntegrable (fun x => Real.exp (-4 * x) *
          ((4 * b0 - b1) + (4 * b1 - 2 * b2) * x + (4 * b2 - 3 * b3) * x ^ 2 +
            (4 * b3 - 4 * b4) * x ^ 3 + (4 * b4 - 5 * b5) * x ^ 4 + 4 * b5 * x ^ 5))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp
  ring

lemma exp_neg_four_bounds : 0.0183 < Real.exp (-4) ∧ Real.exp (-4) < 0.0184 := by
  have h : Real.exp (-4) = Real.exp (-1) ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  have l := Real.exp_neg_one_gt_d9
  have u := Real.exp_neg_one_lt_d9
  have p : 0 < Real.exp (-1) := Real.exp_pos _
  rw [h]
  constructor
  · nlinarith [pow_le_pow_left₀ (by norm_num) l.le 4]
  · have := pow_lt_pow_left₀ u p.le (by norm_num : (4 : ℕ) ≠ 0)
    nlinarith

lemma betaStar_eq : betaStar = 13 / 32 - Real.exp (-4) * (13 / 32 + 5 / 8 + 1 / 4 + 0 + 0 + 0) := by
  unfold betaStar
  rw [← integral_exp_poly (13 / 32) (5 / 8) (1 / 4) 0 0 0]
  apply intervalIntegral.integral_congr
  intro x _
  simp only
  have : Real.exp (-2 * x) ^ 2 = Real.exp (-4 * x) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc (Real.exp (-2 * x) + x * Real.exp (-2 * x)) ^ 2
      = Real.exp (-2 * x) ^ 2 * (1 + x) ^ 2 := by ring
    _ = _ := by rw [this]; ring

/-- The integral `F(y) = ∫₀¹ (e^{-x(2-y)} + x e^{-x(2-y)})² dx`. -/
noncomputable def F (ye : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (Real.exp (-(x * (2 - ye))) + x * Real.exp (-(x * (2 - ye)))) ^ 2

lemma F_nonneg (ye : ℝ) : 0 ≤ F ye := by
  unfold F
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x _; positivity

lemma F_lower (ye : ℝ) (hy : 0 ≤ ye) :
    (17*ye^3/128 + 13*ye^2/64 + 19*ye/64 + 13/32) - Real.exp (-4) *
      ((17*ye^3/128 + 13*ye^2/64 + 19*ye/64 + 13/32) + (17*ye^3/32 + 13*ye^2/16 + 19*ye/16 + 5/8)
        + (17*ye^3/16 + 13*ye^2/8 + 11*ye/8 + 1/4) + (17*ye^3/12 + 3*ye^2/2 + ye/2)
        + (13*ye^3/12 + ye^2/2) + ye^3/3) ≤ F ye := by
  rw [← integral_exp_poly]
  unfold F
  apply intervalIntegral.integral_mono_on (by norm_num)
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop
  intro x hx
  obtain ⟨hx0, _⟩ := hx
  have hu : 0 ≤ 2 * x * ye := by positivity
  have hexp := Real.sum_le_exp_of_nonneg hu 4
  simp [Finset.sum_range_succ, Nat.factorial] at hexp
  have hsplit : (Real.exp (-(x * (2 - ye))) + x * Real.exp (-(x * (2 - ye)))) ^ 2
      = Real.exp (-4 * x) * (Real.exp (2 * x * ye) * (1 + x) ^ 2) := by
    have : Real.exp (-(x * (2 - ye))) ^ 2 = Real.exp (-4 * x) * Real.exp (2 * x * ye) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
    calc (Real.exp (-(x * (2 - ye))) + x * Real.exp (-(x * (2 - ye)))) ^ 2
        = Real.exp (-(x * (2 - ye))) ^ 2 * (1 + x) ^ 2 := by ring
      _ = _ := by rw [this]; ring
  rw [hsplit]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hx2 : 0 ≤ (1 + x) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_right hexp hx2
  nlinarith [this]

end OfflineStochMatch.Attenuation.Eq22Aux

open OfflineStochMatch.Attenuation OfflineStochMatch.Attenuation.Eq22Aux in
theorem solution (aT : ℝ → ℝ) (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) :
    (∀ ye ∈ Set.Icc (0 : ℝ) 1,
      betaStar ≤ aT ye * ∫ x in (0 : ℝ)..1,
        (Real.exp (-(x * (2 - ye))) + x * Real.exp (-(x * (2 - ye)))) ^ 2) ∧
    aT 0 * (∫ x in (0 : ℝ)..1,
        (Real.exp (-(x * (2 - 0))) + x * Real.exp (-(x * (2 - 0)))) ^ 2) = betaStar := by
  have haT0 : aT 0 = 1 := by
    rcases haT with h | h <;> subst h <;> simp [expAtt, linAtt]
  have haTlin : ∀ ye, 1 - 1 / 2 * ye ≤ aT ye := by
    intro ye
    rcases haT with h | h <;> subst h
    · unfold expAtt
      have := Real.add_one_le_exp (-(1 / 2 * ye)); linarith
    · simp [linAtt]
  refine ⟨?_, ?_⟩
  · intro ye hye
    obtain ⟨h0, h1⟩ := hye
    have hF := F_lower ye h0
    have hFn := F_nonneg ye
    change betaStar ≤ aT ye * F ye
    have hlin : (1 - 1 / 2 * ye) * F ye ≤ aT ye * F ye :=
      mul_le_mul_of_nonneg_right (haTlin ye) hFn
    have hc : 0 ≤ 1 - 1 / 2 * ye := by linarith
    have hmain : betaStar ≤ (1 - 1 / 2 * ye) * F ye := by
      rw [betaStar_eq]
      obtain ⟨El, Eu⟩ := exp_neg_four_bounds
      set E := Real.exp (-4)
      have hm := mul_le_mul_of_nonneg_left hF hc
      refine le_trans ?_ hm
      have hy2 : ye ^ 2 ≤ 1 := by nlinarith
      have hy3 : ye ^ 3 ≤ 1 := by nlinarith
      have hy3' : 0 ≤ ye ^ 3 := by positivity
      have hy2' : 0 ≤ ye ^ 2 := by positivity
      -- (1 - y/2) * lower - I0 = y * Q(y), with Q ≥ 0 on [0,1]
      have hQ : 0 ≤ 3/32 - 87*E/32 + ye*(7/128 - 379*E/128) + ye^2*(1/32 - 215*E/96)
          + ye^3*(1751*E/768 - 17/256) := by
        nlinarith [mul_nonneg h0 (by linarith : (0:ℝ) ≤ 7/128 - 379*E/128)]
      have key : (1 - 1 / 2 * ye) * ((17*ye^3/128 + 13*ye^2/64 + 19*ye/64 + 13/32) - E *
          ((17*ye^3/128 + 13*ye^2/64 + 19*ye/64 + 13/32) + (17*ye^3/32 + 13*ye^2/16 + 19*ye/16 + 5/8)
            + (17*ye^3/16 + 13*ye^2/8 + 11*ye/8 + 1/4) + (17*ye^3/12 + 3*ye^2/2 + ye/2)
            + (13*ye^3/12 + ye^2/2) + ye^3/3))
          - (13 / 32 - E * (13 / 32 + 5 / 8 + 1 / 4 + 0 + 0 + 0))
          = ye * (3/32 - 87*E/32 + ye*(7/128 - 379*E/128) + ye^2*(1/32 - 215*E/96)
          + ye^3*(1751*E/768 - 17/256)) := by ring
      nlinarith [mul_nonneg h0 hQ]
    linarith
  · rw [haT0, one_mul]
    unfold betaStar
    apply intervalIntegral.integral_congr
    intro x _
    simp only
    congr 2 <;> ring_nf
