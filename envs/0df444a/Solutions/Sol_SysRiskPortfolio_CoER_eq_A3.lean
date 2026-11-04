-- Prove2me | solution 1 for SysRiskPortfolio.CoER.eq_A3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T07:01:54.383384+00:00
-- url     : https://prove2.me/submissions/d7e9c51d-d1f7-42bd-a7fb-1fbbe14675a6

import Mathlib
import Definitions.Def_SysRiskPortfolio_CoER_BivariateNormal

open MeasureTheory ProbabilityTheory SysRiskPortfolio.CoER

theorem solution (mux muy sx sy rho y : ℝ) (hx : 0 < sx) (hy : 0 < sy) (hr : |rho| < 1) : condLaw mux muy sx sy rho y = ProbabilityTheory.gaussianReal (mux + rho * sx * (y - muy) / sy) ⟨sx ^ 2 * (1 - rho ^ 2), mul_nonneg (sq_nonneg sx) (by have h := abs_lt.mp hr; nlinarith)⟩ := by
  have hr2 : 0 < 1 - rho ^ 2 := by have h := abs_lt.mp hr; nlinarith
  set M := mux + rho * sx * (y - muy) / sy with hM
  set V : NNReal := ⟨sx ^ 2 * (1 - rho ^ 2), mul_nonneg (sq_nonneg sx) (by have h := abs_lt.mp hr; nlinarith)⟩ with hV
  set W : NNReal := ⟨sy ^ 2, sq_nonneg sy⟩ with hW
  have hVv : (V : ℝ) = sx ^ 2 * (1 - rho ^ 2) := rfl
  have hWv : (W : ℝ) = sy ^ 2 := rfl
  have hVpos : (0 : ℝ) < V := by rw [hVv]; positivity
  have hWpos : (0 : ℝ) < W := by rw [hWv]; positivity
  have hV0 : V ≠ 0 := by intro h; rw [h] at hVpos; simp at hVpos
  have hW0 : W ≠ 0 := by intro h; rw [h] at hWpos; simp at hWpos
  -- factorization of the joint density
  have hfac : ∀ t, bvnPDF mux muy sx sy rho t y = gaussianPDFReal M V t * gaussianPDFReal muy W y := by
    intro t
    simp only [bvnPDF, gaussianPDFReal]
    rw [hVv, hWv]
    have hs : Real.sqrt (2 * Real.pi * (sx ^ 2 * (1 - rho ^ 2))) * Real.sqrt (2 * Real.pi * sy ^ 2)
        = 2 * Real.pi * sx * sy * Real.sqrt (1 - rho ^ 2) := by
      rw [← Real.sqrt_mul (by positivity)]
      rw [show 2 * Real.pi * (sx ^ 2 * (1 - rho ^ 2)) * (2 * Real.pi * sy ^ 2)
          = (2 * Real.pi * sx * sy) ^ 2 * (1 - rho ^ 2) by ring]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [mul_mul_mul_comm, ← Real.exp_add, ← mul_inv, hs, one_div]
    congr 2
    rw [hM]
    field_simp
    ring
  have hint : ∫ t, bvnPDF mux muy sx sy rho t y = gaussianPDFReal muy W y := by
    simp_rw [hfac]
    rw [integral_mul_const, integral_gaussianPDFReal_eq_one M hV0, one_mul]
  have hGpos := gaussianPDFReal_pos muy W y hW0
  rw [gaussianReal_of_var_ne_zero _ hV0, condLaw]
  congr 1
  funext x
  rw [gaussianPDF, condPDF, hint, hfac, mul_div_assoc, div_self hGpos.ne', mul_one]
