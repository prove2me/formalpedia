-- Prove2me | solution 1 for PI.AprimeInfW.mulLC_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:18:55.455924+00:00
-- url     : https://prove2.me/submissions/48113044-c887-466d-b1b8-d270f7681403

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
theorem _root_.solution {c : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (Y : Fin m → Fin c → ℂ) :
    mulLC A Y = (A * Matrix.of Y : Matrix (Fin m) (Fin c) ℂ) := by
  ext j i
  simp [mulLC, trC, mulRC, Matrix.vecMul, Matrix.mulVec, Matrix.mul_apply, dotProduct, mul_comm]
end PI.AprimeInfW
