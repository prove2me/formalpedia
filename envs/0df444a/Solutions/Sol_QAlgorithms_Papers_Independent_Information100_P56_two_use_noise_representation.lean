-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P56.two_use_noise_representation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:28:39.545955+00:00
-- url     : https://prove2.me/submissions/e76ff23a-f442-4e33-a00a-b8f2414d3d1e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section


open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Section VI E, p.17: the two-use exchangeable-noise representation criterion.
A fixed complement is allowed. At b=1/4, a=c=1/4 and lambda=1/2 need no division. -/
theorem solution (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + 2 * b + c = 1) :
    (∀ lambda mu : ℝ,
      ((1 - mu) * (1 - lambda) ^ 2 + mu * lambda ^ 2) -
        ((1 - mu) * lambda ^ 2 + mu * (1 - lambda) ^ 2) =
          (1 - 2 * mu) * (1 - 2 * lambda)) ∧
    (b ≤ 1 / 4 → |a - c| ≤ Real.sqrt (1 - 4 * b) →
      ∃ lambda ∈ Set.Icc (0 : ℝ) (1 / 2), ∃ mu ∈ Set.Icc (0 : ℝ) (1 / 2),
        ∃ flip : Bool,
          b = lambda * (1 - lambda) ∧
          (if flip then c else a) = (1 - mu) * (1 - lambda) ^ 2 + mu * lambda ^ 2 ∧
          (if flip then a else c) = (1 - mu) * lambda ^ 2 + mu * (1 - lambda) ^ 2) := by
  refine ⟨fun l m => by ring, fun hb4 habs => ?_⟩
  set s := Real.sqrt (1 - 4 * b) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = 1 - 4 * b := Real.sq_sqrt (by linarith)
  have hs1 : s ≤ 1 := by nlinarith
  have hlam : b = (1 - s) / 2 * (1 - (1 - s) / 2) := by nlinarith
  rcases eq_or_lt_of_le hs0 with h0 | hpos
  · have hac : a = c := by
      have := abs_nonneg (a - c); rw [← h0] at habs
      have : |a - c| = 0 := le_antisymm habs this
      linarith [abs_eq_zero.mp this]
    refine ⟨(1 - s) / 2, ⟨by linarith, by linarith⟩, 0, ⟨le_refl _, by norm_num⟩, false, hlam, ?_, ?_⟩
    · simp; rw [← h0]; nlinarith
    · simp; rw [← h0]; nlinarith
  · set μ := (1 - |a - c| / s) / 2 with hμ
    have hq : |a - c| / s ≤ 1 := by rw [div_le_one hpos]; exact habs
    have hq0 : 0 ≤ |a - c| / s := div_nonneg (abs_nonneg _) hs0
    have hkey : (1 - 2 * μ) * s = |a - c| := by
      rw [hμ]; field_simp; ring
    refine ⟨(1 - s) / 2, ⟨by linarith, by linarith⟩, μ, ⟨by linarith, by linarith⟩, decide (a < c), hlam, ?_, ?_⟩
    · by_cases h : a < c
      · simp [h]; rw [abs_of_neg (by linarith)] at hkey; nlinarith
      · simp [h]; rw [abs_of_nonneg (by linarith)] at hkey; nlinarith
    · by_cases h : a < c
      · simp [h]; rw [abs_of_neg (by linarith)] at hkey; nlinarith
      · simp [h]; rw [abs_of_nonneg (by linarith)] at hkey; nlinarith



end

