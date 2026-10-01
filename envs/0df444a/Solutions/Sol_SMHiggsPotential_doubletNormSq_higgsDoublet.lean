-- Prove2me | solution 1 for SMHiggsPotential.doubletNormSq_higgsDoublet
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T09:43:24.511072+00:00
-- url     : https://prove2.me/submissions/2b8cbaa2-694e-48b7-8ecd-9eb94a597fa5

import Mathlib
import Definitions.Def_SMHiggsPotential_Defs

open Complex SMHiggsPotential

theorem solution (g M H φ0 : ℝ) (φp : ℂ) :
    doubletNormSq (higgsDoublet g M H φ0 φp) =
      2 * M ^ 2 / g ^ 2 + 2 * M / g * H + (1 / 2) * (H ^ 2 + φ0 ^ 2 + 2 * normSq φp) := by
  -- Expand definitions
  dsimp [doubletNormSq, higgsDoublet, vev]
  -- sum over Fin 2
  rw [Fin.sum_univ_two]
  -- Φ 0 = φp, Φ 1 = ((v+H)+iφ0)/√2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  -- divide by √2
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hdiv :
      normSq ((((2 * M / g + H : ℝ) : ℂ) + ↑φ0 * I) / ↑(Real.sqrt 2)) =
        normSq (((2 * M / g + H : ℝ) : ℂ) + ↑φ0 * I) / 2 := by
    calc
      normSq ((((2 * M / g + H : ℝ) : ℂ) + ↑φ0 * I) / ↑(Real.sqrt 2))
          = normSq (((2 * M / g + H : ℝ) : ℂ) + ↑φ0 * I) / normSq (↑(Real.sqrt 2) : ℂ) := by
              rw [normSq_div]
      _ = normSq (((2 * M / g + H : ℝ) : ℂ) + ↑φ0 * I) / (Real.sqrt 2) ^ 2 := by
              simp [Complex.normSq_ofReal]
      _ = normSq (((2 * M / g + H : ℝ) : ℂ) + ↑φ0 * I) / 2 := by
              rw [Real.sq_sqrt h2]
  rw [hdiv]
  -- |x + y I|^2 = x^2 + y^2
  have hsq :
      normSq (((2 * M / g + H : ℝ) : ℂ) + ↑φ0 * I) = (2 * M / g + H) ^ 2 + φ0 ^ 2 := by
    rw [Complex.normSq_add_mul_I]
  rw [hsq]
  ring
