-- Prove2me | solution 1 for PI.SqPairLocal.conj_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:58.835651+00:00
-- url     : https://prove2.me/submissions/e3473df1-010d-47f3-82d4-a0d962829e90

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_DivAtOneOfInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PI.SqPairLocal
theorem _root_.solution {N : ℕ} (u e : Matrix (Fin N) (Fin N) E) (hu : uᴴ * u = 1) :
    uᴴ * e * u + (uᴴ * e * u)ᴴ - 1 = uᴴ * (e + eᴴ - 1) * u := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    mul_sub, mul_add, sub_mul, add_mul, mul_one, hu]
  simp only [mul_assoc]
end PI.SqPairLocal
