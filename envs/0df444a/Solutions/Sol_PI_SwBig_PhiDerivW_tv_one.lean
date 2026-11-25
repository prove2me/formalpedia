-- Prove2me | solution 1 for PI.SwBig.PhiDerivW.tv_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:34.133708+00:00
-- url     : https://prove2.me/submissions/990f07af-8bf4-4609-9f9a-60f79c17e533

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
theorem _root_.solution : tv k r 1 = 1 := by
  funext i
  unfold tv
  split_ifs <;> simp
end PI.SwBig.PhiDerivW
