-- Prove2me | solution 1 for PI.KerFourSqW.exists_quat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:56:59.927798+00:00
-- url     : https://prove2.me/submissions/4680d15e-a2a2-4587-b164-07f2f7cf3484

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_QuatMatTransposeMul
import Theorems.Thm_PI_KerFourSqW_quatMat_transpose_mul
import Theorems.Thm_PI_KerFourSqW_rat_sum_four_squares

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
theorem _root_.solution (a : ℚ) (ha : 0 < a) :
    ∃ Q : Matrix (Fin 4) (Fin 4) ℚ, Qᵀ * Q = a • (1 : Matrix (Fin 4) (Fin 4) ℚ) := by
  obtain ⟨r₁, r₂, r₃, r₄, h⟩ := rat_sum_four_squares a ha
  exact ⟨quatMat r₁ r₂ r₃ r₄, by rw [quatMat_transpose_mul, h]⟩
end PI.KerFourSqW
