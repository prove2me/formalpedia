-- Prove2me | solution 1 for PGDRevision20261113.asymmetric_interior_algebraic_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-13T09:50:12.263495+00:00
-- url     : https://prove2.me/submissions/866d9a14-062c-4da3-8353-99ebb04f09bd

import Theorems.Thm_PGDRevision20261113_asymmetric_interior_coefficient_certificate
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option maxHeartbeats 6000000
open PGDRevision20261113
open scoped BigOperators

private lemma factor_upper (u : ℝ) (hu : 1 ≤ u) :
    asymDenominator u * (asymUpper u ^ 2 - (1 - 5 / 66) ^ 2 * asymV2 u) =
      16 * (u - 2) ^ 2 * asymQPlus u := by
  have hu0 : u ≠ 0 := ne_of_gt (by linarith)
  have hd : u ^ 2 + 1 ≠ 0 := ne_of_gt (by positivity)
  dsimp [asymDenominator, asymUpper, asymS, asymB, asymV2, asymQPlus,
    evalDescending, asymPlusCoefficients]
  field_simp
  <;> ring

private lemma factor_lower (u : ℝ) (hu : 1 ≤ u) :
    asymDenominator u * ((1 + 5 / 66) ^ 2 * asymV2 u - asymLower u ^ 2) =
      16 * (u - 2) ^ 2 * asymQMinus u := by
  have hu0 : u ≠ 0 := ne_of_gt (by linarith)
  have hd : u ^ 2 + 1 ≠ 0 := ne_of_gt (by positivity)
  dsimp [asymDenominator, asymLower, asymS, asymB, asymV2, asymQMinus,
    evalDescending, asymMinusCoefficients]
  field_simp
  <;> ring

private lemma upper_pos (u : ℝ) (hu : 1 ≤ u) : 0 < asymUpper u := by
  have hs : asymS u < 1 := by
    unfold asymS
    apply (div_lt_iff₀ (by positivity : 0 < u ^ 2 + 1)).2
    nlinarith
  have hb : 0 ≤ asymB u := by unfold asymB; positivity
  unfold asymUpper
  nlinarith [sq_nonneg (asymS u)]

private lemma qplus_pos (u : ℝ) (hu : 1 ≤ u) : 0 < asymQPlus u := by
  have hu0 : 0 < u := by linarith
  dsimp [asymQPlus, evalDescending, asymPlusCoefficients]
  positivity

private lemma qminus_pos (u : ℝ) (hu : 1 ≤ u) (hu6 : u ≤ 6) : 0 < asymQMinus u := by
  by_cases he : u = 6
  · subst u
    norm_num [asymQMinus, evalDescending, asymMinusCoefficients]
  have hu6' : u < 6 := lt_of_le_of_ne hu6 he
  let z := (u - 1) / 5
  have hz0 : 0 ≤ z := by dsimp [z]; linarith
  have hz1 : 0 < 1 - z := by dsimp [z]; linarith
  have heq : 1 + 5 * z = u := by dsimp [z]; ring
  have hb := PGDRevision20261113.asymmetric_interior_coefficient_certificate
  rcases hb with ⟨_, _, _, _, _, _, _, hb, _⟩
  rw [← heq, hb]
  norm_num [asymBernsteinCoefficients, Fin.sum_univ_succ, Nat.choose]
  positivity

private lemma lower_neg (u : ℝ) (hu : 6 ≤ u) : asymLower u < 0 := by
  let z := u - 6
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have htail : 0 < -(evalDescending asymTailCoefficients z) := by
    dsimp [evalDescending, asymTailCoefficients]
    ring_nf
    positivity
  have hb := PGDRevision20261113.asymmetric_interior_coefficient_certificate
  rcases hb with ⟨_, _, _, _, _, _, _, _, _, _, _, hb⟩
  have hid := hb z hz
  have heq : 6 + z = u := by dsimp [z]; ring
  rw [heq] at hid
  have hm : 0 < 1375 * u ^ 2 * (u ^ 2 + 1) ^ 2 := by
    have : 0 < u := by linarith
    positivity
  have hn : 1375 * u ^ 2 * (u ^ 2 + 1) ^ 2 * asymLower u < 0 := by linarith
  by_contra hh
  have hp := mul_nonneg (le_of_lt hm) (le_of_not_gt hh)
  linarith

theorem solution : AsymmetricInteriorFactorizationClaim := by
  intro u hu
  have hU := upper_pos u hu
  have hP := qplus_pos u hu
  have hM := qminus_pos u hu
  have hL := lower_neg u
  have hfu := factor_upper u hu
  have hfl := factor_lower u hu
  have hu0 : 0 < u := by linarith
  have hD : 0 < asymDenominator u := by unfold asymDenominator; positivity
  have hv : 0 ≤ asymV2 u := by unfold asymV2; positivity
  have hs := Real.sq_sqrt hv
  have hs0 := Real.sqrt_nonneg (asymV2 u)
  refine ⟨hfu, hfl, hU, hP, hM, hL, ?_, ?_⟩
  · have hprod : 0 ≤ asymDenominator u *
        (asymUpper u ^ 2 - (1 - 5 / 66) ^ 2 * asymV2 u) := by
      rw [hfu]
      positivity
    have hsquare : 0 ≤ asymUpper u ^ 2 - (1 - 5 / 66) ^ 2 * asymV2 u :=
      (mul_nonneg_iff_of_pos_left hD).mp hprod
    nlinarith
  · by_cases h6 : u ≤ 6
    · have hq : 0 < asymQMinus u := hM h6
      have hprod : 0 ≤ asymDenominator u *
          ((1 + 5 / 66) ^ 2 * asymV2 u - asymLower u ^ 2) := by
        rw [hfl]
        positivity
      have hsquare : 0 ≤ (1 + 5 / 66) ^ 2 * asymV2 u - asymLower u ^ 2 :=
        (mul_nonneg_iff_of_pos_left hD).mp hprod
      nlinarith
    · have hn := hL (le_of_not_ge h6)
      nlinarith
