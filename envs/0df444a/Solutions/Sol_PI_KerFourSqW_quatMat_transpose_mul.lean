-- Prove2me | solution 1 for PI.KerFourSqW.quatMat_transpose_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:48:42.848913+00:00
-- url     : https://prove2.me/submissions/f541473f-3699-433f-a23b-91d3316c9cf1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QuatMatTransposeMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open PI PI.KerFourSqW
namespace PI.KerFourSqW
theorem _root_.solution (r₁ r₂ r₃ r₄ : ℚ) :
    (quatMat r₁ r₂ r₃ r₄)ᵀ * quatMat r₁ r₂ r₃ r₄ = (r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2 + r₄ ^ 2) • (1 : Matrix (Fin 4) (Fin 4) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quatMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> ring
end PI.KerFourSqW
