-- Prove2me | solution 1 for PI.AprimeInfW.det_mulLC_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:11.707848+00:00
-- url     : https://prove2.me/submissions/0fe7b6ac-8771-40f0-9bb8-370fb3f9f079

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_TupPlace
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_DetMulRCReal
import Theorems.Thm_PI_AprimeInfW_det_mulRC

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
theorem _root_.solution {c : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    ((mulLC (c := c) A).restrictScalars ℝ).det = Complex.normSq A.det ^ c := by
  rw [LinearMap.det_restrictScalars, mulLC, LinearMap.det_conj, det_mulRC, Matrix.det_transpose, map_pow,
    Algebra.norm_complex_apply]
end PI.AprimeInfW
