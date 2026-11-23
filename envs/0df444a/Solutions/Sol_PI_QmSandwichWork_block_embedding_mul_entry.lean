-- Prove2me | solution 1 for PI.QmSandwichWork.block_embedding_mul_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:18.681555+00:00
-- url     : https://prove2.me/submissions/da9c7ae4-a9c0-4266-a9fa-16b79996f4cb

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
theorem _root_.solution (M N : Matrix (Fin 2) (Fin 2) A) : (E1 M * E2 N) (0, 0) (0, 0) = M 0 0 * N 0 0 := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, E1, E2]
end PI.QmSandwichWork
