-- Prove2me | solution 1 for PI.PC.phi_intervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:08:15.545859+00:00
-- url     : https://prove2.me/submissions/759d919b-b81d-497d-9cd1-6661c5ffffb3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_ChebyshevPrimeBoundsLogFact
import Theorems.Thm_PI_PC_phi_integrableOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PC
open Real MeasureTheory Set
namespace PI.PC
theorem _root_.solution {p q : ℝ} (hp : 2 ≤ p) (hpq : p ≤ q) :
    IntervalIntegrable phi volume p q := by
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpq).mpr (phi_integrableOn q hp)
end PI.PC
