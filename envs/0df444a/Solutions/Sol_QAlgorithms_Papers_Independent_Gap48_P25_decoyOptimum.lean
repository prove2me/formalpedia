-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P25.decoyOptimum
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T23:15:31.215289+00:00
-- url     : https://prove2.me/submissions/ee9f6ff9-484d-45cf-9d49-633d66f1674d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

open QAlgorithms.Papers.Independent.Gap48.P25
noncomputable section


open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Eqs.(38)–(39), PDF p.30: decoy proxy optimizer, critical root and linear scaling. -/
theorem solution (nu s Q : ℝ) (hnu : 0 < nu) (hs : 0 < s) (hs1 : s ≤ 1)
    (hQ : Q ∈ Set.Icc (0 : ℝ) 1) (hh : QAlgorithms.binEntropy2 Q < 1/2) :
    0 < decoyOptimizer Q ∧
    decoyProxy nu s Q (decoyOptimizer Q) = nu*s*decoyOptimizer Q*(1-2*QAlgorithms.binEntropy2 Q)/2 ∧
    (∀ mu : ℝ, 0 ≤ mu → decoyProxy nu s Q mu ≤ decoyProxy nu s Q (decoyOptimizer Q)) ∧
    (∀ mu : ℝ, 0 ≤ mu → (decoyProxy nu s Q mu =
      decoyProxy nu s Q (decoyOptimizer Q) ↔ mu = decoyOptimizer Q)) ∧
    decoyProxy nu s Q (2*decoyOptimizer Q) = 0 ∧
    (∀ t b : ℝ, decoyProxy nu (t*b) Q (decoyOptimizer Q) = t*decoyProxy nu b Q (decoyOptimizer Q)) := by
  set h := QAlgorithms.binEntropy2 Q with hdef
  have hA : 0 < 1 - h := by linarith
  have h12 : 0 < 1 - 2*h := by linarith
  have hm : decoyOptimizer Q = (1 - 2*h) / (2*(1-h)) := by
    unfold decoyOptimizer; rw [← hdef]; field_simp; ring
  have hP : ∀ mu, decoyProxy nu s Q mu = nu*s*(mu*(1-2*h) - (1-h)*mu^2) := by
    intro mu; unfold decoyProxy; rw [← hdef]; ring
  have hns : 0 < nu*s := mul_pos hnu hs
  have key : ∀ mu, decoyProxy nu s Q (decoyOptimizer Q) - decoyProxy nu s Q mu =
      nu*s*(1-h)*(mu - decoyOptimizer Q)^2 := by
    intro mu; rw [hP, hP, hm]; field_simp; ring
  refine ⟨?_, ?_, fun mu _ => ?_, fun mu _ => ?_, ?_, fun t b => ?_⟩
  · rw [hm]; positivity
  · rw [hP, hm]; field_simp; ring
  · have := key mu
    have : 0 ≤ nu*s*(1-h)*(mu - decoyOptimizer Q)^2 := by positivity
    linarith
  · constructor
    · intro he
      have k := key mu
      rw [he, sub_self] at k
      have : (mu - decoyOptimizer Q)^2 = 0 := by
        have hpos : 0 < nu*s*(1-h) := mul_pos hns hA
        nlinarith [sq_nonneg (mu - decoyOptimizer Q)]
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      linarith
    · rintro rfl; rfl
  · rw [hP, hm]; field_simp; ring
  · unfold decoyProxy; ring



