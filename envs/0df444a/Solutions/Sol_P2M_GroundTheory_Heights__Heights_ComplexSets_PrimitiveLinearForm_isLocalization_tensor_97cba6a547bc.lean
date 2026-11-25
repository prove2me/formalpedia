-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_PrimitiveLinearForm_isLocalization_tensor_97cba6a547bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:23:03.545167+00:00
-- url     : https://prove2.me/submissions/e41d0ce0-6748-4750-bb1e-8f56b9e826f2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PrimitiveLinearForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open Polynomial TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveLinearForm
variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
attribute [local instance] tensorRightAlgebra
namespace GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveLinearForm
theorem _root_.solution :
    IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) (FractionRing R ⊗[R] B) := by
  refine isLocalizedModule_iff_isLocalization.mp ?_
  have h := (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) (FractionRing R)
    (IsScalarTower.toAlgHom R B (FractionRing R ⊗[R] B)).toLinearMap).mpr ?_
  · exact h
  · exact TensorProduct.isBaseChange R B (FractionRing R)
end GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveLinearForm
