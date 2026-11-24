-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.FC.pm_mulVec_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:59:57.625957+00:00
-- url     : https://prove2.me/submissions/a0c74e91-592a-4740-bf6f-1dee0e1de9c2

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
theorem _root_.solution (j : Fin (2 * r + k + 1)) :
    Pm k r e f wf z0 *ᵥ Pi.single j 1 = fcol k r e f wf z0 j := by
  rw [Matrix.mulVec_single_one]
  rfl
end PI.NUnimodLoc.UnitaryGroupMassFormula.FC
