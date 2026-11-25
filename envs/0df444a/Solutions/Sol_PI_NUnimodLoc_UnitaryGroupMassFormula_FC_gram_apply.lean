-- Prove2me | solution 1 for PI.NUnimodLoc.UnitaryGroupMassFormula.FC.gram_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:28.063579+00:00
-- url     : https://prove2.me/submissions/68da072a-e70e-406c-ad56-465bc00690f0

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
theorem _root_.solution (i j : Fin (2 * r + k + 1)) :
    ((Pm k r e f wf z0)ᴴ * Jm ε * Pm k r e f wf z0) i j =
      hJ ε (fcol k r e f wf z0 i) (fcol k r e f wf z0 j) := by
  rw [Matrix.mul_apply]
  simp only [hJ, Jm, Matrix.mul_diagonal, Matrix.mulVec_diagonal, dotProduct,
    Matrix.conjTranspose_apply, Pm, Matrix.of_apply, Pi.star_apply]
  refine Finset.sum_congr rfl (fun s _ => by ring)
end PI.NUnimodLoc.UnitaryGroupMassFormula.FC
