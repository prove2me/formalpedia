-- Prove2me | solution 1 for PI.SSE.rel_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:40.785287+00:00
-- url     : https://prove2.me/submissions/5a57f2e0-72a9-4c55-85ab-3af86f714388

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_LatExt
import Theorems.Thm_PI_SSE_qf_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Classical
open PI PI.SSE
namespace PI.SSE
theorem _root_.solution (G : ℂ → ℂ) (A ω s s' : ℂ) (hA : A ≠ 0) (hss : s * s' = 1)
    (hω : ∀ z, G (z + ω) = s * (qf A ω z * G z)) :
    ∀ z, G (z + -ω) = s' * (qf A (-ω) z * G z) := by
  intro z
  have h := hω (z + -ω)
  rw [neg_add_cancel_right] at h
  rw [h, show s' * (qf A (-ω) z * (s * (qf A ω (z + -ω) * G (z + -ω)))) =
      (s * s') * (qf A ω (z + -ω) * qf A (-ω) z) * G (z + -ω) by ring, hss, qf_neg A ω z hA]
  ring
end PI.SSE
