-- Prove2me | solution 1 for PI.AprimeInfW.det_mulRC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:21:25.25355+00:00
-- url     : https://prove2.me/submissions/f8682690-69db-43bd-94ac-3b268b1afd6f

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
theorem _root_.solution (A : Matrix (Fin m) (Fin m) ℂ) : (mulRC (r := r) A).det = A.det ^ r := by
  rw [mulRC, LinearMap.det_pi]
  have h : A.vecMulLinear = Matrix.toLin' Aᵀ := by
    ext v i
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  simp [h, LinearMap.det_toLin', Matrix.det_transpose]
end PI.AprimeInfW
