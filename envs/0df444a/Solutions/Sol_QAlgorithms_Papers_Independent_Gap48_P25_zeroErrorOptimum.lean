-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P25.zeroErrorOptimum
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T23:15:26.737741+00:00
-- url     : https://prove2.me/submissions/4218f4a2-06b2-4a48-b5f6-ee1138df6adb

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

open QAlgorithms.Papers.Independent.Gap48.P25
noncomputable section


open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- IV.B.4, PDF p.29: exact optimization of the zero-error weak-pulse proxy. -/
theorem solution (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    zeroProxy s s = s^2/2 ∧
    (∀ mu : ℝ, 0 ≤ mu → zeroProxy s mu ≤ s^2/2) ∧
    (∀ mu : ℝ, 0 ≤ mu → (zeroProxy s mu = s^2/2 ↔ mu = s)) ∧
    (∀ t b : ℝ, (t*b)^2/2 = t^2*(b^2/2)) := by
  refine ⟨by unfold zeroProxy; ring, fun mu _ => ?_, fun mu _ => ?_, fun t b => by ring⟩
  · unfold zeroProxy; nlinarith [sq_nonneg (mu - s)]
  · unfold zeroProxy
    constructor
    · intro h
      have : (mu - s) ^ 2 = 0 := by nlinarith
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      linarith
    · rintro rfl; ring



