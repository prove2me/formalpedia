-- Prove2me | solution 1 for PI.AprimeInfW.mulRC_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:18:59.834979+00:00
-- url     : https://prove2.me/submissions/85239c47-1f00-413d-83d6-e078d8f31453

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_TupPlace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_DetMulRCReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW
open MeasureTheory Matrix
variable {r m : ℕ}
namespace PI.AprimeInfW
theorem _root_.solution (A : Matrix (Fin m) (Fin m) ℂ) (Y : Fin r → Fin m → ℂ) :
    mulRC A Y = (Matrix.of Y * A : Matrix (Fin r) (Fin m) ℂ) := by
  ext i j
  simp [mulRC, Matrix.vecMul, Matrix.mul_apply, dotProduct]
end PI.AprimeInfW
