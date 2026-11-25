-- Prove2me | solution 1 for PI.SwBig.PhiDerivW.diagC_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:22.265026+00:00
-- url     : https://prove2.me/submissions/408907f7-3fec-4d20-88c3-e113dddf6b31

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PhiDerivative_StarinvDeriv

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
open PI PI.SwBig PI.SwBig.PhiDerivW
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable (k r : ℕ)
namespace PI.SwBig.PhiDerivW
theorem _root_.solution (v : Fin (2 * r + k + 1) → ℂ) : diagC k r v = Matrix.diagonal v := by
  simp [diagC]
end PI.SwBig.PhiDerivW
