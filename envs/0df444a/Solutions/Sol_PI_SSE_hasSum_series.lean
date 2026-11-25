-- Prove2me | solution 1 for PI.SSE.hasSum_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:22:49.659861+00:00
-- url     : https://prove2.me/submissions/47d94d0f-0258-4121-8716-d261255e6de2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaNz
import Theorems.Thm_PI_SSE_term_pos
import Theorems.Thm_PI_SSE_term_neg

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
theorem _root_.solution (τ : ℂ) (hτ : 0 < τ.im) :
    HasSum (fun n : ℕ => 2 * Real.pi * I * ((2 * (n : ℂ) + 1) * ((-1) ^ n * qe τ n)))
      (jacobiTheta₂' (1 / 2 + τ / 2) τ) := by
  have h := (hasSum_jacobiTheta₂'_term (1 / 2 + τ / 2) hτ).nat_add_neg_add_one
  convert h using 1
  funext n
  rw [term_pos, term_neg]
  ring
end PI.SSE
