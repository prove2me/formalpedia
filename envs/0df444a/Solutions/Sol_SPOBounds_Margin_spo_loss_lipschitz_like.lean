-- Prove2me | solution 1 for SPOBounds.Margin.spo_loss_lipschitz_like
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:14:21.991377+00:00
-- url     : https://prove2.me/submissions/b8070c80-6bf5-41be-bcff-ec0bd963e80f

import Mathlib
import Definitions.Def_SPOBounds_Margin_Model
import Definitions.Def_SPOBounds_Margin_Degeneracy

namespace SPOBounds.Margin

/-- Theorem 3(a) multiplied out: the oracle is Lipschitz-like under the strength property. -/
theorem aux_spoll_oracle_lip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (μ : ℝ) (hμ : 0 < μ) (hstr : StrengthProperty S μ w)
    (c₁ c₂ : StrongDual ℝ E) :
    μ * min (nu S c₁) (nu S c₂) * ‖w c₁ - w c₂‖ ≤ ‖c₁ - c₂‖ := by
  have h1 := hstr c₁ (w c₂) (hw c₂).1
  have h2 := hstr c₂ (w c₁) (hw c₁).1
  have hn : ‖w c₂ - w c₁‖ = ‖w c₁ - w c₂‖ := norm_sub_rev _ _
  rw [hn] at h1
  have hsum : c₁ (w c₂ - w c₁) + c₂ (w c₁ - w c₂) = (c₁ - c₂) (w c₂ - w c₁) := by
    simp only [ContinuousLinearMap.sub_apply, map_sub]
    ring
  have hop : (c₁ - c₂) (w c₂ - w c₁) ≤ ‖c₁ - c₂‖ * ‖w c₁ - w c₂‖ := by
    have := (c₁ - c₂).le_opNorm (w c₂ - w c₁)
    rw [hn] at this
    exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using this)
  set d := ‖w c₁ - w c₂‖ with hd
  set m := min (nu S c₁) (nu S c₂) with hm
  have hd0 : 0 ≤ d := norm_nonneg _
  have hm1 : m ≤ nu S c₁ := min_le_left _ _
  have hm2 : m ≤ nu S c₂ := min_le_right _ _
  have hd2 : 0 ≤ d ^ 2 := sq_nonneg _
  have key : μ * m * d ^ 2 ≤ ‖c₁ - c₂‖ * d := by
    have e1 : μ * m / 2 * d ^ 2 ≤ μ * nu S c₁ / 2 * d ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hd2
      have := mul_le_mul_of_nonneg_left hm1 hμ.le
      linarith
    have e2 : μ * m / 2 * d ^ 2 ≤ μ * nu S c₂ / 2 * d ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hd2
      have := mul_le_mul_of_nonneg_left hm2 hμ.le
      linarith
    linarith
  rcases hd0.lt_or_eq with hpos | hzero
  · have : μ * m * d * d ≤ ‖c₁ - c₂‖ * d := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero, mul_zero]
    exact norm_nonneg _

end SPOBounds.Margin

open SPOBounds.Margin

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (S : Set E) (hS : S.Nonempty) (hSc : IsCompact S) (hSv : Convex ℝ S) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (μ : ℝ) (hμ : 0 < μ) (hstr : StrengthProperty S μ w)
    (c c₁ c₂ : StrongDual ℝ E) :
    μ * min (nu S c₁) (nu S c₂) * |spoLoss w c₁ c - spoLoss w c₂ c| ≤
      ‖c‖ * ‖c₁ - c₂‖ := by
  have hlip := aux_spoll_oracle_lip S w hw μ hμ hstr c₁ c₂
  have hm0 : 0 ≤ min (nu S c₁) (nu S c₂) :=
    le_min Metric.infDist_nonneg Metric.infDist_nonneg
  have hA : 0 ≤ μ * min (nu S c₁) (nu S c₂) := mul_nonneg hμ.le hm0
  have heq : spoLoss w c₁ c - spoLoss w c₂ c = c (w c₁ - w c₂) := by
    simp only [spoLoss, map_sub]
    ring
  have hb : |spoLoss w c₁ c - spoLoss w c₂ c| ≤ ‖c‖ * ‖w c₁ - w c₂‖ := by
    rw [heq, ← Real.norm_eq_abs]
    exact c.le_opNorm _
  calc μ * min (nu S c₁) (nu S c₂) * |spoLoss w c₁ c - spoLoss w c₂ c|
      ≤ μ * min (nu S c₁) (nu S c₂) * (‖c‖ * ‖w c₁ - w c₂‖) :=
        mul_le_mul_of_nonneg_left hb hA
    _ = ‖c‖ * (μ * min (nu S c₁) (nu S c₂) * ‖w c₁ - w c₂‖) := by ring
    _ ≤ ‖c‖ * ‖c₁ - c₂‖ := mul_le_mul_of_nonneg_left hlip (norm_nonneg _)
