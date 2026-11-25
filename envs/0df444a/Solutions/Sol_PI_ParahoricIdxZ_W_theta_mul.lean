-- Prove2me | solution 1 for PI.ParahoricIdxZ.W.theta_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:04:07.251708+00:00
-- url     : https://prove2.me/submissions/f10d3b56-ed52-4408-ae52-bc74cf46c80e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)
namespace PI.ParahoricIdxZ.W
theorem _root_.solution {a t : ℕ} {R : Type} [CommRing R] (A A' : Matrix (Fin a) (Fin a) R)
    (B B' : Matrix (Fin a) (Fin t) R) (C C' : Matrix (Fin t) (Fin a) R)
    (D D' : Matrix (Fin t) (Fin t) R) :
    theta A B C D * theta A' B' C' D' =
      theta (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  simp only [theta, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
end PI.ParahoricIdxZ.W
