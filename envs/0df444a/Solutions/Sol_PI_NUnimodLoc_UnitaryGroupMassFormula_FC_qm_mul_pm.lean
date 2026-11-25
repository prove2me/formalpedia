-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.FC.qm_mul_pm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:14:07.678117+00:00
-- url     : https://prove2.me/submissions/95d7c2b8-fbd7-498f-9dc3-1755ee90baad

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_FrameC
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_gram_eq_Hpk
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_Hpk_mul_self


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
theorem _root_.solution : Qm k r ε e f wf z0 * Pm k r e f wf z0 = 1 := by
  unfold Qm
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (Jm ε), gram_eq_Hpk hF, Hpk_mul_self]
end PI.NUnimodLoc.UnitaryGroupMassFormula.FC
