-- Prove2me | solution 1 for SpenglerVertical.DoubleMarginalization.linear_demand_elasticity
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:46:55.775014+00:00
-- url     : https://prove2.me/submissions/cb271f7e-3de5-45cc-8745-5c8d2050b9c2

import Definitions.Def_SpenglerVertical_DoubleMarginalization_Model

set_option autoImplicit false
open SpenglerVertical.DoubleMarginalization

private theorem linear_profit_square (a b c p : ℝ) :
    profit (linearDemand a b) c p =
      b * ((a - c) ^ 2 / 4 - (p - (a + c) / 2) ^ 2) := by
  unfold profit linearDemand
  ring

private theorem ratio_shift (a c d : ℝ) (h1 : a - c - d ≠ 0) (h2 : a - c ≠ 0)
    (h3 : a + c ≠ 0) :
    ((a + (c + d)) / (a - (c + d))) / ((a + c) / (a - c)) =
      1 + (2 * a * d) / ((a - c - d) * (a + c)) := by
  have h4 : a - (c + d) ≠ 0 := by simpa only [sub_add_eq_sub_sub] using h1
  field_simp
  ring

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∀ c p : ℝ, IsProfitMax (linearDemand a b) c p ↔ p = (a + c) / 2) ∧
    (∀ p : ℝ, marginalRevenue (linearDemand a b) p = 2 * p - a) ∧
    (∀ c : ℝ, c < a →
      elasticity (linearDemand a b) ((a + c) / 2) = (a + c) / (a - c)) ∧
    elasticity (linearDemand a b) (a / 2) = 1 ∧
    (∀ c c' : ℝ, 0 ≤ c → c < c' → c' < a →
      elasticity (linearDemand a b) ((a + c') / 2) / elasticity (linearDemand a b) ((a + c) / 2)
        > ((a + c') / 2) / ((a + c) / 2)) ∧
    (∀ c c' Δ : ℝ, 0 ≤ c → c < c' → 0 < Δ → c' + Δ < a →
      elasticity (linearDemand a b) ((a + (c' + Δ)) / 2) / elasticity (linearDemand a b) ((a + c') / 2)
        > elasticity (linearDemand a b) ((a + (c + Δ)) / 2) / elasticity (linearDemand a b) ((a + c) / 2)) := by
  have hderiv (p : ℝ) : deriv (linearDemand a b) p = -b := by
    have h : HasDerivAt (linearDemand a b) (-b) p := by
      convert ((hasDerivAt_const p a).sub (hasDerivAt_id p)).const_mul b using 1 <;> first | rfl | ring
    exact h.deriv
  have hel (c : ℝ) (hc : c < a) :
      elasticity (linearDemand a b) ((a + c) / 2) = (a + c) / (a - c) := by
    unfold elasticity
    rw [hderiv]
    unfold linearDemand
    have hhalf : a - (a + c) / 2 = (a - c) / 2 := by ring
    rw [hhalf]
    field_simp [ne_of_gt hb, ne_of_gt (sub_pos.mpr hc)]
  refine ⟨?_, ?_, hel, ?_, ?_, ?_⟩
  · intro c p
    constructor
    · intro h
      have hi := h ((a + c) / 2)
      rw [linear_profit_square, linear_profit_square] at hi
      have hs : 0 ≤ (p - (a + c) / 2) ^ 2 := sq_nonneg _
      have he : (p - (a + c) / 2) ^ 2 = 0 := by nlinarith
      nlinarith
    · intro h
      subst p
      intro x
      rw [linear_profit_square, linear_profit_square]
      nlinarith [mul_nonneg (le_of_lt hb) (sq_nonneg (x - (a + c) / 2))]
  · intro p
    unfold marginalRevenue
    rw [hderiv]
    unfold linearDemand
    field_simp [ne_of_gt hb]
    ring
  · simpa [ne_of_gt ha] using hel 0 ha
  · intro c c' hc hcc' hc'a
    rw [hel c' hc'a, hel c (lt_trans hcc' hc'a)]
    have hac : 0 < a + c := by linarith
    have hac' : 0 < a + c' := by linarith
    have hminc : 0 < a - c := by linarith
    have hminc' : 0 < a - c' := by linarith
    have hid : ((a + c') / (a - c')) / ((a + c) / (a - c)) -
        ((a + c') / 2) / ((a + c) / 2) =
        (a + c') * (c' - c) / ((a - c') * (a + c)) := by
      field_simp
      ring
    have hp : 0 < (a + c') * (c' - c) / ((a - c') * (a + c)) := by positivity
    linarith
  · intro c c' d hc hcc' hd hc'd
    have hc'a : c' < a := by linarith
    have hcda : c + d < a := by linarith
    have hca : c < a := by linarith
    rw [hel (c' + d) hc'd, hel c' hc'a, hel (c + d) hcda, hel c hca]
    have h1 : 0 < a - c' - d := by linarith
    have h2 : 0 < a - c - d := by linarith
    have h3 : 0 < a + c' := by linarith
    have h4 : 0 < a + c := by linarith
    rw [ratio_shift a c' d (ne_of_gt h1) (by linarith) (ne_of_gt h3),
      ratio_shift a c d (ne_of_gt h2) (by linarith) (ne_of_gt h4)]
    have hdenlt : (a - c' - d) * (a + c') < (a - c - d) * (a + c) := by
      nlinarith [mul_pos (sub_pos.mpr hcc') (show 0 < c' + c + d by linarith)]
    have hleft : 0 < (a - c' - d) * (a + c') := mul_pos h1 h3
    have hright : 0 < (a - c - d) * (a + c) := mul_pos h2 h4
    have hnum : 0 < 2 * a * d := by positivity
    have hfrac : (2 * a * d) / ((a - c - d) * (a + c)) <
        (2 * a * d) / ((a - c' - d) * (a + c')) := by
      apply (div_lt_div_iff₀ hright hleft).2
      exact mul_lt_mul_of_pos_left hdenlt hnum
    linarith

