-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.FC.pm_mulVec_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:00:07.21819+00:00
-- url     : https://prove2.me/submissions/e04ee71d-b922-4bde-90ba-657ffbb11347

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_FrameC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.NUnimodLoc PI.NUnimodLoc.UnitaryGroupMassFormula PI.NUnimodLoc.UnitaryGroupMassFormula.FC
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW Formalism.REAL
variable {k r : ℕ}
variable {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}
namespace PI.NUnimodLoc.UnitaryGroupMassFormula.FC
theorem _root_.solution (c : Fin (2 * r + k + 1) → ℂ) :
    Pm k r e f wf z0 *ᵥ c = ∑ j, c j • fcol k r e f wf z0 j := by
  funext a
  simp [Pm, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
end PI.NUnimodLoc.UnitaryGroupMassFormula.FC
