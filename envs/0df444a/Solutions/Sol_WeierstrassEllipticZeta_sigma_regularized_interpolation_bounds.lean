-- Prove2me | solution 1 for WeierstrassEllipticZeta.sigma_regularized_interpolation_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T01:09:05.299038+00:00
-- url     : https://prove2.me/submissions/cf0be1a9-003f-4092-a3aa-edb0f88e5a35

import Definitions.Def_WeierstrassEllipticZeta_PolynomialInterpolation
import Theorems.Thm_WeierstrassEllipticZeta_exists_elliptic_sigma_quadratic_growth
import Theorems.Thm_WeierstrassEllipticZeta_sigma_regularized_coordinates_entire
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_sigma_regularized_polynomial_interpolation
import Theorems.Thm_WeierstrassEllipticZeta_cleared_sigma_polynomial_interpolation

open Set WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair) :
    ∃ (D : EllipticSigmaDifferentialData L) (R₀ c₁₃ c₁₄ : ℝ),
      0 < R₀ ∧ 1 < c₁₃ ∧ 1 < c₁₄ ∧
      SigmaPolynomialInterpolation L D.sigma c₁₃ R₀ ∧
      ClearedSigmaPolynomialInterpolation L D.sigma c₁₄ R₀ := by
  obtain ⟨D, A, hA, hgrowth⟩ := exists_elliptic_sigma_quadratic_growth L
  obtain ⟨S, hS, hrel, h0, h1, h2, hSb⟩ :=
    sigma_regularized_coordinates_entire L D (hasDerivAt_weierstrassZeta L)
  let B := 9*A+24
  have hB : 0 < B := by dsimp [B]; positivity
  have hb (z : ℂ) : ‖D.sigma z‖ ≤ Real.exp (B*(1+‖z‖^2)) ∧
      ∀ j, ‖S j z‖ ≤ Real.exp (B*(1+‖z‖^2)) := by
    refine ⟨(hgrowth z).trans ?_, hSb A hA.le hgrowth z⟩
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right (show A ≤ B by dsimp [B]; linarith)
    positivity
  have hσ : AnalyticOnNhd ℂ D.sigma univ :=
    D.entire.differentiableOn.analyticOnNhd isOpen_univ
  refine ⟨D, 1, Real.exp (15*B), Real.exp (30*B+128), by norm_num,
    Real.one_lt_exp_iff.mpr (by positivity),
    Real.one_lt_exp_iff.mpr (by positivity), ?_, ?_⟩
  · exact sigma_regularized_polynomial_interpolation L D.sigma S hσ hS hrel B hB hb
  · exact cleared_sigma_polynomial_interpolation L D.sigma S hσ hS hrel B hB hb
