-- Prove2me | solution 1 for PI.SSE.th_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:50.382169+00:00
-- url     : https://prove2.me/submissions/7ac92b60-a553-4d5f-8722-7df0d5fe8a6a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaA

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
theorem _root_.solution (τ u : ℂ) : th τ (-u) = -th τ u := by
  unfold th
  have h1 : jacobiTheta₂ (u + (1 / 2 + τ / 2)) τ =
      cexp (-↑Real.pi * I * (τ + 2 * (u - (1 / 2 + τ / 2)))) * jacobiTheta₂ (u - (1 / 2 + τ / 2)) τ := by
    rw [show u + (1 / 2 + τ / 2) = (u - (1 / 2 + τ / 2) + τ) + 1 by ring, jacobiTheta₂_add_left,
      jacobiTheta₂_add_left']
  rw [show -u + (1 / 2 + τ / 2) = -(u - (1 / 2 + τ / 2)) by ring, jacobiTheta₂_neg_left, h1]
  have key : cexp (↑Real.pi * I * u) * cexp (-↑Real.pi * I * (τ + 2 * (u - (1 / 2 + τ / 2)))) =
      -cexp (↑Real.pi * I * -u) := by
    calc cexp (↑Real.pi * I * u) * cexp (-↑Real.pi * I * (τ + 2 * (u - (1 / 2 + τ / 2))))
        = cexp (↑Real.pi * I * -u + ↑Real.pi * I) := by
          rw [← Complex.exp_add]
          congr 1
          ring
      _ = -cexp (↑Real.pi * I * -u) := by
          rw [Complex.exp_add, Complex.exp_pi_mul_I]
          ring
  rw [← mul_assoc, key]
  ring
end PI.SSE
