-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P25.noDecoyOptimum
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T23:15:32.698056+00:00
-- url     : https://prove2.me/submissions/4dd91257-1461-4ec9-ad38-8f983679e10c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

open QAlgorithms.Papers.Independent.Gap48.P25
noncomputable section


open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Eqs.(36)–(37), PDF p.29: source quadratic's maximum and optimizer, with
informative entropy domain. The equality F=0 is allowed. -/
theorem solution (nu s Q : ℝ) (hnu : 0 < nu) (hs : 0 < s) (hs1 : s ≤ 1)
    (hQ : 0 ≤ Q ∧ Q < 1/4) (hA : 0 < 1-QAlgorithms.binEntropy2 (2*Q))
    (hF : 0 ≤ noDecoyF Q) :
    0 ≤ noDecoyOptimizer s Q ∧
    noDecoyProxy nu s Q (noDecoyOptimizer s Q) = nu*s*noDecoyOptimizer s Q*noDecoyF Q/2 ∧
    (∀ mu : ℝ, 0 ≤ mu → noDecoyProxy nu s Q mu ≤ noDecoyProxy nu s Q (noDecoyOptimizer s Q)) ∧
    (∀ mu : ℝ, 0 ≤ mu → (noDecoyProxy nu s Q mu =
      noDecoyProxy nu s Q (noDecoyOptimizer s Q) ↔ mu = noDecoyOptimizer s Q)) ∧
    noDecoyProxy nu s Q (2*noDecoyOptimizer s Q) = 0 ∧
    noDecoyProxy nu s Q (noDecoyOptimizer s Q) =
      s^2*(nu*(noDecoyF Q)^2/(2*(1-QAlgorithms.binEntropy2 (2*Q)))) := by
  set h := QAlgorithms.binEntropy2 (2*Q) with hdef
  set F := noDecoyF Q with hF'
  have hm : noDecoyOptimizer s Q = s*F/(1-h) := by unfold noDecoyOptimizer; rw [← hdef, ← hF']
  have hP : ∀ mu, noDecoyProxy nu s Q mu = nu*(mu*s*F - mu^2*(1-h)/2) := by
    intro mu; unfold noDecoyProxy; rw [← hdef, ← hF']
  have key : ∀ mu, noDecoyProxy nu s Q (noDecoyOptimizer s Q) - noDecoyProxy nu s Q mu =
      nu*(1-h)/2*(mu - noDecoyOptimizer s Q)^2 := by
    intro mu; rw [hP, hP, hm]; field_simp; ring
  refine ⟨?_, ?_, fun mu _ => ?_, fun mu _ => ?_, ?_, ?_⟩
  · rw [hm]; exact div_nonneg (mul_nonneg hs.le hF) hA.le
  · rw [hP, hm]; field_simp; ring
  · have := key mu
    have : 0 ≤ nu*(1-h)/2*(mu - noDecoyOptimizer s Q)^2 := by
      have := hA.le; positivity
    linarith
  · constructor
    · intro he
      have k := key mu
      rw [he, sub_self] at k
      have hpos : 0 < nu*(1-h)/2 := by positivity
      have : (mu - noDecoyOptimizer s Q)^2 = 0 := by
        nlinarith [sq_nonneg (mu - noDecoyOptimizer s Q)]
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      linarith
    · rintro rfl; rfl
  · rw [hP, hm]; field_simp; ring
  · rw [hP, hm]; field_simp; ring



