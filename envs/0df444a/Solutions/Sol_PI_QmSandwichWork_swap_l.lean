-- Prove2me | solution 1 for PI.QmSandwichWork.swap_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:06:50.544582+00:00
-- url     : https://prove2.me/submissions/44cfff58-239c-4b51-908d-dd8c83e2d145

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RTTIndependence
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_RttRelation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EntrywiseSandwichCommute_BlockEmbeddingMulEntrySwap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.QmSandwichWork
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P.W
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace PI.QmSandwichWork
theorem _root_.solution {x y : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A} (h : x * y = y * x)
    (Z : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) : x * (y * Z) = y * (x * Z) := by
  rw [← Matrix.mul_assoc, h, Matrix.mul_assoc]
end PI.QmSandwichWork
