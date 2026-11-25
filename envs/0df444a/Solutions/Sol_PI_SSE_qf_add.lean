-- Prove2me | solution 1 for PI.SSE.qf_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:16:59.776571+00:00
-- url     : https://prove2.me/submissions/25a123f1-aad1-442c-acb7-49538d873193

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_LatExt

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
theorem _root_.solution (A ω v z : ℂ) (hA : A ≠ 0) :
    qf A v (z + ω) * qf A ω z =
      cexp (Real.pi * ((starRingEnd ℂ) v * ω - (starRingEnd ℂ) ω * v) / (2 * A)) *
        qf A (ω + v) z := by
  simp only [qf, map_add]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  field_simp
  ring
end PI.SSE
