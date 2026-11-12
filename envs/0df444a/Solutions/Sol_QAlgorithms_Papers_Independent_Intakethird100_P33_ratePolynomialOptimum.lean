-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P33.ratePolynomialOptimum
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T02:04:28.950201+00:00
-- url     : https://prove2.me/submissions/d10c59b9-f713-4250-8109-01e877bc0e2f

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P33

noncomputable section

open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Intakethird100.P33 in
theorem solution (t tB eta f : ℝ)
    (ht : 0 < t) (ht1 : t < 1) (htB : 0 < tB) (htB1 : tB ≤ 1)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hf : 0 ≤ f) (hf1 : f < 1) :
    let muOpt := 1 / (2 * (1 - t))
    0 < muOpt ∧
    ratePolynomial t tB eta f muOpt = t * tB * eta * (1 - f) / (4 * (1 - t)) ∧
    (∀ mu : ℝ, 0 ≤ mu →
      ratePolynomial t tB eta f mu ≤ ratePolynomial t tB eta f muOpt) ∧
    (∀ mu : ℝ, 0 ≤ mu →
      (ratePolynomial t tB eta f mu = ratePolynomial t tB eta f muOpt ↔ mu = muOpt)) := by
  intro muOpt
  have hmdef : muOpt = 1 / (2 * (1 - t)) := rfl
  clear_value muOpt
  have ha : 0 < 1 - t := by linarith
  have hK : 0 < t * tB * eta * (1 - f) :=
    mul_pos (mul_pos (mul_pos ht htB) heta) (by linarith)
  have h2a : (2 * (1 - t)) ≠ 0 := mul_ne_zero two_ne_zero ha.ne'
  have hm : muOpt * (2 * (1 - t)) = 1 := by
    rw [hmdef, one_div, inv_mul_cancel₀ h2a]
  have hval : ratePolynomial t tB eta f muOpt = t * tB * eta * (1 - f) / (4 * (1 - t)) := by
    unfold ratePolynomial
    rw [eq_div_iff (mul_ne_zero four_ne_zero ha.ne')]
    linear_combination (-(t * tB * eta * (1 - f)) * (muOpt * (2 * (1 - t)) - 1)) * hm
  have hdiff : ∀ mu, ratePolynomial t tB eta f muOpt - ratePolynomial t tB eta f mu =
      t * tB * eta * (1 - f) * (1 - t) * (mu - muOpt) ^ 2 := by
    intro mu
    unfold ratePolynomial
    linear_combination (t * tB * eta * (1 - f) * (mu - muOpt)) * hm
  refine ⟨?_, hval, ?_, ?_⟩
  · rw [hmdef]
    exact one_div_pos.mpr (by positivity)
  · intro mu _
    have h1 := hdiff mu
    have h2 : 0 ≤ t * tB * eta * (1 - f) * (1 - t) * (mu - muOpt) ^ 2 :=
      mul_nonneg (mul_nonneg hK.le ha.le) (sq_nonneg _)
    linarith
  · intro mu _
    constructor
    · intro h
      have h1 := hdiff mu
      rw [h, sub_self] at h1
      have hKa : t * tB * eta * (1 - f) * (1 - t) ≠ 0 := (mul_pos hK ha).ne'
      have h2 : (mu - muOpt) ^ 2 = 0 := by
        rcases mul_eq_zero.mp h1.symm with h3 | h3
        · exact absurd h3 hKa
        · exact h3
      have h4 : mu - muOpt = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h2
      linarith
    · intro h
      rw [h]

end
