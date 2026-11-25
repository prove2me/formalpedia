-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.FC.colm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:38.763339+00:00
-- url     : https://prove2.me/submissions/ce8727e4-84f7-4a52-82a3-41924b5a3dc3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_FrameC
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_pm_mulVec_single
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_qm_mulVec_fcol

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
theorem _root_.solution (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (Qm k r ε e f wf z0 *ᵥ ((g - 1) *ᵥ fcol k r e f wf z0 j)) i =
      (Qm k r ε e f wf z0 * g * Pm k r e f wf z0) i j - (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, qm_mulVec_fcol hF,
    ← pm_mulVec_single (e := e) (f := f) (wf := wf) (z0 := z0) j, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Pi.sub_apply, Matrix.mulVec_single_one]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]
end PI.NUnimodLoc.UnitaryGroupMassFormula.FC
