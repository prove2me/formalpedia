-- Prove2me | solution 1 for PI.QmSandwichWork.flip_row
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:18.608586+00:00
-- url     : https://prove2.me/submissions/1b2d62ab-4f73-4a1f-8306-147957316987

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
theorem _root_.solution (D : ℂ) (K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) :
    ((D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) * K) (0, 0) (0, 0) =
      algebraMap ℂ A (D - 1) * K (0, 0) (0, 0) := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Pf, Matrix.one_apply,
    Algebra.algebraMap_eq_smul_one, sub_smul, sub_mul, smul_mul_assoc]
end PI.QmSandwichWork
