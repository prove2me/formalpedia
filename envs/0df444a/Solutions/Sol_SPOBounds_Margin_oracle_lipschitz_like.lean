-- Prove2me | solution 1 for SPOBounds.Margin.oracle_lipschitz_like
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T10:58:27.777958+00:00
-- url     : https://prove2.me/submissions/28031a28-cc1a-4c6d-a93e-72ede8ffcbac

import Mathlib
import Definitions.Def_SPOBounds_Margin_Model
import Definitions.Def_SPOBounds_Margin_Degeneracy

set_option autoImplicit false

open SPOBounds.Margin in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (S : Set E) (hS : S.Nonempty) (hSc : IsCompact S) (hSv : Convex ℝ S) (hSnt : S.Nontrivial)
    (w : StrongDual ℝ E → E) (hw : IsOracle S w)
    (μ : ℝ) (hμ : 0 < μ) (hstr : StrengthProperty S μ w)
    (c₁ c₂ : StrongDual ℝ E) :
    μ * min (nu S c₁) (nu S c₂) * ‖w c₁ - w c₂‖ ≤ ‖c₁ - c₂‖ := by
  have h1 := hstr c₁ (w c₂) (hw c₂).1
  have h2 := hstr c₂ (w c₁) (hw c₁).1
  have hn1 : 0 ≤ nu S c₁ := Metric.infDist_nonneg
  have hn2 : 0 ≤ nu S c₂ := Metric.infDist_nonneg
  set d := ‖w c₁ - w c₂‖ with hd
  have hd1 : ‖w c₂ - w c₁‖ = d := norm_sub_rev _ _
  rw [hd1] at h1
  have hcs : (c₁ - c₂) (w c₂ - w c₁) ≤ ‖c₁ - c₂‖ * d := by
    have := (c₁ - c₂).le_opNorm (w c₂ - w c₁)
    rw [hd1, Real.norm_eq_abs] at this
    exact le_trans (le_abs_self _) this
  have hsum : c₁ (w c₂ - w c₁) + c₂ (w c₁ - w c₂) = (c₁ - c₂) (w c₂ - w c₁) := by
    simp only [ContinuousLinearMap.sub_apply, map_sub]
    ring
  have hmin : min (nu S c₁) (nu S c₂) ≤ (nu S c₁ + nu S c₂) / 2 := by
    have := min_le_left (nu S c₁) (nu S c₂)
    have := min_le_right (nu S c₁) (nu S c₂)
    linarith
  have hd0 : 0 ≤ d := norm_nonneg _
  have hm0 : 0 ≤ min (nu S c₁) (nu S c₂) := le_min hn1 hn2
  have key : μ * min (nu S c₁) (nu S c₂) * d * d ≤ ‖c₁ - c₂‖ * d := by
    have e1 : μ * min (nu S c₁) (nu S c₂) * d * d ≤ μ * ((nu S c₁ + nu S c₂) / 2) * d ^ 2 := by
      have : μ * min (nu S c₁) (nu S c₂) ≤ μ * ((nu S c₁ + nu S c₂) / 2) :=
        mul_le_mul_of_nonneg_left hmin hμ.le
      nlinarith [mul_nonneg hd0 hd0]
    nlinarith
  rcases hd0.eq_or_lt with h | h
  · rw [← h]; simp
  · exact le_of_mul_le_mul_right key h
