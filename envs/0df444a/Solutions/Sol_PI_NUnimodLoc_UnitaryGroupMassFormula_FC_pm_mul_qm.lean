-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.FC.pm_mul_qm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:30:14.725719+00:00
-- url     : https://prove2.me/submissions/ace88104-c239-4f48-ae0b-7977a6c6bdec

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_FrameC
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_qm_mul_pm

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
variable (hF : IsFrameJ ε e f wf z0)
include hF
namespace PI.NUnimodLoc.UnitaryGroupMassFormula.FC
theorem _root_.solution : Pm k r e f wf z0 * Qm k r ε e f wf z0 = 1 := mul_eq_one_comm.mp (qm_mul_pm hF)
end PI.NUnimodLoc.UnitaryGroupMassFormula.FC
