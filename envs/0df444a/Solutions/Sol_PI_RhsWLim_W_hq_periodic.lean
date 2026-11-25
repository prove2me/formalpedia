-- Prove2me | solution 1 for PI.RhsWLim.W.hq_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:15:47.366608+00:00
-- url     : https://prove2.me/submissions/bdd25240-c097-4555-9f5c-029c44987ddb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
namespace PI.RhsWLim.W
theorem _root_.solution (k : ℕ) (T' : ℝ) (y : Fin k → ℂ) (θ : ℝ) : hq k T' y (θ + 2 * Real.pi) = hq k T' y θ := by
  have key : Complex.exp (((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I) = Complex.exp ((θ : ℂ) * Complex.I) := by
    have e : (((θ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I = θ * Complex.I + 2 * Real.pi * Complex.I := by
      push_cast; ring
    rw [e, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  unfold hq
  rw [key]
end PI.RhsWLim.W
