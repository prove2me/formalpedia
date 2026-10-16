-- Prove2me | solution 1 for OAI.WeightedGenerator.negative_quartic_bounded
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T04:51:35.585374+00:00
-- url     : https://prove2.me/submissions/08316ba0-22d5-4f80-9b23-cade4c17d359

-- Source proof: OpenAI/math contributors, Minimum.lean lines 907–961,
-- commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
-- Platform adaptation and verification directed by Alexander Richard Towell (queelius),
-- performed with Codex. No new mathematical argument is claimed.
import Mathlib.Tactic

theorem solution (a b c d : ℝ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → -4*t^4+a*t^3+b*t^2+c*t+d ≤ C := by
  let S : ℝ := 1+|a|+|b|+|c|+|d|
  have hS : 1 ≤ S := by dsimp [S]; linarith [abs_nonneg a, abs_nonneg b, abs_nonneg c, abs_nonneg d]
  have ha : a ≤ |a| := le_abs_self a
  have hb : b ≤ |b| := le_abs_self b
  have hc : c ≤ |c| := le_abs_self c
  have hd : d ≤ |d| := le_abs_self d
  have hsa : 0 ≤ |a| := abs_nonneg a
  have hsb : 0 ≤ |b| := abs_nonneg b
  have hsc : 0 ≤ |c| := abs_nonneg c
  have hsd : 0 ≤ |d| := abs_nonneg d
  refine ⟨S*(S^3+S^2+S+1), ?_⟩
  intro t ht
  have htop : -4*t^4+a*t^3+b*t^2+c*t+d ≤ |a| *t^3+|b| *t^2+|c| *t+|d| := by
    nlinarith [mul_le_mul_of_nonneg_right ha (pow_nonneg ht 3),
      mul_le_mul_of_nonneg_right hb (sq_nonneg t), mul_le_mul_of_nonneg_right hc ht,
      pow_nonneg ht 4]
  have hC : 0 ≤ S*(S^3+S^2+S+1) := by positivity
  by_cases h : t ≤ S
  · have h₁ : |a| *t^3 ≤ S*S^3 := by
      apply mul_le_mul
      · dsimp [S]; linarith
      · exact pow_le_pow_left₀ ht h 3
      · positivity
      · linarith
    have h₂ : |b| *t^2 ≤ S*S^2 := by
      apply mul_le_mul
      · dsimp [S]; linarith
      · exact pow_le_pow_left₀ ht h 2
      · positivity
      · linarith
    have h₃ : |c| *t ≤ S*S := by
      apply mul_le_mul
      · dsimp [S]; linarith
      · exact h
      · exact ht
      · linarith
    have h₄ : |d| ≤ S := by dsimp [S]; linarith
    nlinarith
  · have htS : S ≤ t := (lt_of_not_ge h).le
    have ht1 : 1 ≤ t := hS.trans htS
    have ht2 : t ≤ t^2 := by nlinarith
    have ht3 : t^2 ≤ t^3 := by nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht1)]
    have h₁ := mul_le_mul_of_nonneg_left ht3 hsb
    have h₂ := mul_le_mul_of_nonneg_left (ht2.trans ht3) hsc
    have h₃ := mul_le_mul_of_nonneg_left (ht1.trans (ht2.trans ht3)) hsd
    have h₄ : (|a|+|b|+|c|+|d|)*t^3 ≤ t^4 := by
      have hs : |a|+|b|+|c|+|d| ≤ t := by dsimp [S] at htS; linarith
      simpa only [← pow_succ'] using mul_le_mul_of_nonneg_right hs (pow_nonneg ht 3)
    have ht4 : 0 ≤ t^4 := pow_nonneg ht 4
    have hlead : a*t^3+b*t^2+c*t+d ≤ (|a|+|b|+|c|+|d|)*t^3 := by
      nlinarith [mul_le_mul_of_nonneg_right ha (pow_nonneg ht 3),
        mul_le_mul_of_nonneg_right hb (sq_nonneg t), mul_le_mul_of_nonneg_right hc ht]
    nlinarith
