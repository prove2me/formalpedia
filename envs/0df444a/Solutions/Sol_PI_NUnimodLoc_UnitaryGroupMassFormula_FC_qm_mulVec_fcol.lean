-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.FC.qm_mulVec_fcol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:25:49.782334+00:00
-- url     : https://prove2.me/submissions/736f607f-f3bf-48fb-a2a1-e1c9eab74337

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_FrameC
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_pm_mulVec_single
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
theorem _root_.solution (j : Fin (2 * r + k + 1)) :
    Qm k r ε e f wf z0 *ᵥ fcol k r e f wf z0 j = Pi.single j 1 := by
  rw [← pm_mulVec_single (e := e) (f := f) (wf := wf) (z0 := z0) j, Matrix.mulVec_mulVec, qm_mul_pm hF,
    Matrix.one_mulVec]
end PI.NUnimodLoc.UnitaryGroupMassFormula.FC
