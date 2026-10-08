-- Prove2me | solution 1 for UniformDRO.LowerBound.kl_second_branch
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-06T21:33:48.940678+00:00
-- url     : https://prove2.me/submissions/ddf5713f-afe5-4558-a97f-b517ced28342

import Mathlib
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_UniformDRO_LowerBound_Setting

open UniformDRO.LowerBound

/-- Second branch of the KL lower bound: `d(0, δ) = -log(1-δ) ≤ δ/(1-δ) ≤ 2δ` for `0 < δ ≤ 1/2`. -/
theorem solution (δ : ℝ) (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) :
    BanditAlgorithm.bernoulliRelativeEntropy 0 δ = -Real.log (1 - δ) ∧
      -Real.log (1 - δ) ≤ δ / (1 - δ) ∧ δ / (1 - δ) ≤ 2 * δ := by
  have hδ1 : δ < 1 := lt_of_le_of_lt hδh (by norm_num : (1 / 2 : ℝ) < 1)
  have h1δ : 0 < 1 - δ := sub_pos.mpr hδ1
  -- (i) d(0, δ) = log(1/(1-δ)) = -log(1-δ)
  have heq : BanditAlgorithm.bernoulliRelativeEntropy 0 δ = -Real.log (1 - δ) := by
    unfold BanditAlgorithm.bernoulliRelativeEntropy
    have h0 : (0 : ℝ) * Real.log (0 / δ) = 0 := by simp
    simp only [sub_zero, one_mul, h0, zero_add]
    rw [one_div, Real.log_inv]
  -- (ii) -log(1-δ) ≤ δ/(1-δ) via log(1+u) ≤ u with u = δ/(1-δ)
  have hineq1 : -Real.log (1 - δ) ≤ δ / (1 - δ) := by
    set u : ℝ := δ / (1 - δ)
    have hu0 : 0 ≤ u := div_nonneg hδ.le h1δ.le
    have hu1 : 0 < 1 + u := by linarith
    have hrepr : 1 - δ = (1 + u)⁻¹ := by
      dsimp [u]
      field_simp [ne_of_gt h1δ]
      ring
    have hlog : -Real.log (1 - δ) = Real.log (1 + u) := by
      rw [hrepr, Real.log_inv, neg_neg]
    have hle : Real.log (1 + u) ≤ u := by
      have := Real.log_le_sub_one_of_pos hu1
      linarith
    linarith
  -- (iii) δ/(1-δ) ≤ 2δ from δ ≤ 1/2
  have hineq2 : δ / (1 - δ) ≤ 2 * δ := by
    rw [div_le_iff₀ h1δ]
    nlinarith
  exact ⟨heq, hineq1, hineq2⟩
