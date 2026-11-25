-- Prove2me | solution 1 for PI.SSE.term_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:17:27.532455+00:00
-- url     : https://prove2.me/submissions/a90b3ab7-96d3-443b-8f2d-bc0713d79f53

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaNz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex
open PI PI.SSE
namespace PI.SSE
theorem _root_.solution (τ : ℂ) (n : ℕ) :
    jacobiTheta₂'_term (n : ℤ) (1 / 2 + τ / 2) τ
      = 2 * Real.pi * I * (n : ℂ) * ((-1) ^ n * qe τ n) := by
  have hexp : cexp (2 * Real.pi * I * (n : ℂ) * (1 / 2 + τ / 2) + Real.pi * I * (n : ℂ) ^ 2 * τ) =
      (-1) ^ n * qe τ n := by
    rw [qe, show 2 * (Real.pi : ℂ) * I * (n : ℂ) * (1 / 2 + τ / 2) + Real.pi * I * (n : ℂ) ^ 2 * τ =
        (n : ℂ) * (Real.pi * I) + Real.pi * I * τ * ((n : ℂ) * ((n : ℂ) + 1)) by ring,
      Complex.exp_add, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  simp only [jacobiTheta₂'_term, jacobiTheta₂_term, Int.cast_natCast, hexp]
end PI.SSE
