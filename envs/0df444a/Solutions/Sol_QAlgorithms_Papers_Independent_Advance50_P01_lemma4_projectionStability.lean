-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P01.lemma4_projectionStability
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T02:03:40.12634+00:00
-- url     : https://prove2.me/submissions/d937dc05-64b0-44b8-95c8-e8775aa88997

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P01

noncomputable section

open Filter

open scoped Topology

attribute [local instance] Classical.propDecidable

variable {I : Type} [Fintype I] [DecidableEq I]

open QAlgorithms.Papers.Independent.Advance50.P01 in
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (phi varphi : E)
    (hphi : ‖phi‖ = 1) (hvarphi : ‖varphi‖ = 1) (pi : E →L[ℂ] E)
    (hself : ∀ x y, inner ℂ (pi x) y = inner ℂ x (pi y))
    (hidempotent : ∀ x, pi (pi x) = pi x) (epsilon : ℝ)
    (hclose : ‖phi - pi phi‖ ≤ epsilon) :
    ‖rankOneApply phi varphi‖ ^ 2 - ‖pi (rankOneApply phi (pi varphi))‖ ^ 2 ≤
      2 * Real.sqrt 2 * epsilon := by
  obtain ⟨P, hP⟩ : ∃ P, P = pi phi := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = phi - pi phi := ⟨_, rfl⟩
  have hsum : phi = P + Q := by rw [hP, hQ]; abel
  have hPQ : inner ℂ P Q = 0 := by
    rw [hP, hQ, inner_sub_right, hself phi phi, hself phi (pi phi), hidempotent, sub_self]
  have hpyth : ‖P‖ * ‖P‖ + ‖Q‖ * ‖Q‖ = 1 := by
    rw [← norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero P Q hPQ, ← hsum, hphi, mul_one]
  obtain ⟨a, ha⟩ : ∃ a, a = inner ℂ P varphi := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = inner ℂ Q varphi := ⟨_, rfl⟩
  have h1 : ‖rankOneApply phi varphi‖ = ‖a + b‖ := by
    unfold rankOneApply
    rw [norm_smul, hphi, mul_one, ha, hb, ← inner_add_left, ← hsum]
  have h2 : ‖pi (rankOneApply phi (pi varphi))‖ = ‖a‖ * ‖P‖ := by
    unfold rankOneApply
    rw [map_smul, norm_smul, ← hself, ← hP, ha]
  rw [h1, h2]
  have hab1 : ‖a + b‖ ≤ 1 := by
    have := norm_inner_le_norm (𝕜 := ℂ) phi varphi
    rw [hphi, hvarphi, mul_one, hsum, inner_add_left, ← ha, ← hb] at this
    exact this
  have hA : ‖a‖ ≤ ‖P‖ := by
    have := norm_inner_le_norm (𝕜 := ℂ) P varphi
    rw [hvarphi, mul_one, ← ha] at this
    exact this
  have hB : ‖b‖ ≤ ‖Q‖ := by
    have := norm_inner_le_norm (𝕜 := ℂ) Q varphi
    rw [hvarphi, mul_one, ← hb] at this
    exact this
  have hQe : ‖Q‖ ≤ epsilon := by rw [hQ]; exact hclose
  have hA0 := norm_nonneg a
  have hB0 := norm_nonneg b
  have hP0 := norm_nonneg P
  have hQ0 := norm_nonneg Q
  have hab0 := norm_nonneg (a + b)
  have hε0 : 0 ≤ epsilon := le_trans hQ0 hQe
  have hP1 : ‖P‖ ≤ 1 := by nlinarith
  have hA1 : ‖a‖ ≤ 1 := le_trans hA hP1
  have htri : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have hsq : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ hab0 htri 2
  have hbound : ‖a + b‖ ^ 2 - (‖a‖ * ‖P‖) ^ 2 ≤ 2 * epsilon + 2 * epsilon ^ 2 := by
    have e1 : (‖a‖ + ‖b‖) ^ 2 - (‖a‖ * ‖P‖) ^ 2 =
        ‖a‖ ^ 2 * (‖Q‖ * ‖Q‖) + 2 * ‖a‖ * ‖b‖ + ‖b‖ ^ 2 := by
      linear_combination (-‖a‖ ^ 2) * hpyth
    have hA2 : ‖a‖ ^ 2 ≤ 1 := by nlinarith
    have hQ2 : ‖Q‖ * ‖Q‖ ≤ epsilon ^ 2 := by
      have := mul_le_mul hQe hQe hQ0 hε0
      nlinarith
    have e2 : ‖a‖ ^ 2 * (‖Q‖ * ‖Q‖) ≤ epsilon ^ 2 := by
      have := mul_le_mul hA2 hQ2 (mul_nonneg hQ0 hQ0) zero_le_one
      linarith
    have hBe : ‖b‖ ≤ epsilon := le_trans hB hQe
    have e3 : 2 * ‖a‖ * ‖b‖ ≤ 2 * epsilon := by
      have := mul_le_mul hA1 hBe hB0 zero_le_one
      linarith
    have e4 : ‖b‖ ^ 2 ≤ epsilon ^ 2 := by
      have := mul_le_mul hBe hBe hB0 hε0
      nlinarith
    linarith
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have hs15 : Real.sqrt 2 < 3 / 2 := by nlinarith
  have hle1 : ‖a + b‖ ^ 2 - (‖a‖ * ‖P‖) ^ 2 ≤ 1 := by nlinarith
  by_cases hc : 1 ≤ 2 * Real.sqrt 2 * epsilon
  · linarith
  · push_neg at hc
    have hε1 : epsilon ≤ Real.sqrt 2 - 1 := by nlinarith
    have : 2 * epsilon + 2 * epsilon ^ 2 ≤ 2 * Real.sqrt 2 * epsilon := by
      linarith [mul_le_mul_of_nonneg_left hε1 hε0]
    linarith

end
