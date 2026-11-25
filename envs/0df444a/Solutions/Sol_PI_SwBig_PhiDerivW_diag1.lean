-- Prove2me | solution 1 for PI.SwBig.PhiDerivW.diag1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:16.824097+00:00
-- url     : https://prove2.me/submissions/c13a8f23-74bc-43d9-aebb-8778252237b9

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
theorem _root_.solution : Matrix.diagonal (1 : Fin (2 * r + k + 1) → ℂ) = 1 := Matrix.diagonal_one
end PI.SwBig.PhiDerivW
