-- Prove2me | solution 1 for SMHiggsPotential.scalarLagrangian_eq_doublet_potential
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T09:50:10.852707+00:00
-- url     : https://prove2.me/submissions/52f1477d-2051-4296-b0ca-0476ad24c286

import Mathlib
import Definitions.Def_SMHiggsPotential_Defs

open Complex SMHiggsPotential

theorem solution (g M mh βh H φ0 : ℝ) (φp : ℂ) (hM : M ≠ 0) (hg : g ≠ 0) :
    scalarLagrangian g M mh βh H φ0 φp =
      - quarticCoupling g M mh * doubletNormSq (higgsDoublet g M H φ0 φp) ^ 2
        + (mh ^ 2 / 2 - βh) * doubletNormSq (higgsDoublet g M H φ0 φp) := by
  -- First replace doubletNormSq(higgsDoublet) by its closed form
  have hnorm :
      doubletNormSq (higgsDoublet g M H φ0 φp) =
        2 * M ^ 2 / g ^ 2 + 2 * M / g * H + (1 / 2) * (H ^ 2 + φ0 ^ 2 + 2 * normSq φp) := by
    dsimp [doubletNormSq, higgsDoublet, vev]
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have h2 : (0 : ℝ) ≤ 2 := by norm_num
    have hdiv :
        normSq ((((2 * M / g + H : ℝ) : ℂ) + ↑φ0 * I) / ↑(Real.sqrt 2)) =
          normSq (((2 * M / g + H : ℝ) : ℂ) + ↑φ0 * I) / 2 := by
      calc
        _ = normSq (((2 * M / g + H : ℝ) : ℂ) + ↑φ0 * I) / normSq (↑(Real.sqrt 2) : ℂ) := by
            rw [normSq_div]
        _ = normSq (((2 * M / g + H : ℝ) : ℂ) + ↑φ0 * I) / (Real.sqrt 2) ^ 2 := by
            simp [Complex.normSq_ofReal]
        _ = _ := by rw [Real.sq_sqrt h2]
    rw [hdiv, Complex.normSq_add_mul_I]
    ring
  rw [hnorm]
  -- Expand both sides from definitions
  dsimp [scalarLagrangian, quarticCoupling, alphaH]
  -- Clear denominators / normalize
  field_simp [hM, hg]
  ring
