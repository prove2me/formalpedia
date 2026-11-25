-- Prove2me | solution 1 for PI.SSE.term_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:17:24.299128+00:00
-- url     : https://prove2.me/submissions/54595e52-472f-4ffe-893e-8d27ee36e395

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
    jacobiTheta₂'_term (-((n : ℤ) + 1)) (1 / 2 + τ / 2) τ
      = 2 * Real.pi * I * ((n : ℂ) + 1) * ((-1) ^ n * qe τ n) := by
  have hm : cexp (-(Real.pi * I)) = -1 := by
    rw [Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have hexp : cexp (2 * Real.pi * I * (-((n : ℂ) + 1)) * (1 / 2 + τ / 2) +
      Real.pi * I * (-((n : ℂ) + 1)) ^ 2 * τ) = (-1) ^ (n + 1) * qe τ n := by
    rw [qe, show 2 * (Real.pi : ℂ) * I * (-((n : ℂ) + 1)) * (1 / 2 + τ / 2) +
        Real.pi * I * (-((n : ℂ) + 1)) ^ 2 * τ =
        ((n + 1 : ℕ) : ℂ) * (-(Real.pi * I)) + Real.pi * I * τ * ((n : ℂ) * ((n : ℂ) + 1)) by push_cast; ring,
      Complex.exp_add, Complex.exp_nat_mul, hm]
  simp only [jacobiTheta₂'_term, jacobiTheta₂_term, Int.cast_neg, Int.cast_add, Int.cast_natCast,
    Int.cast_one, hexp]
  ring
end PI.SSE
