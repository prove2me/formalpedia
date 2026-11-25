-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.FC.pmH_J_mulVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:36.318729+00:00
-- url     : https://prove2.me/submissions/b75f131e-bfd7-4a42-89e2-34112f935761

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
theorem _root_.solution (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    ((Pm k r e f wf z0)ᴴ *ᵥ (Jm ε *ᵥ y)) i = hJ ε (fcol k r e f wf z0 i) y := by
  rfl
end PI.NUnimodLoc.UnitaryGroupMassFormula.FC
