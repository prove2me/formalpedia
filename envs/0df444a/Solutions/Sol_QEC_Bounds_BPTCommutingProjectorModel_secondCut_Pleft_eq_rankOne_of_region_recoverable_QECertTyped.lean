-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCut_Pleft_eq_rankOne_of_region_recoverable_QECertTyped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:33:49.576284+00:00
-- url     : https://prove2.me/submissions/52d0df0a-55ed-45cf-b27d-ef225ec8442a

import Definitions.Def_QEC_Import_Typed_79c2cc62db33d8d5
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOne
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneWitness
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_eq_rankOne_of_ne_zero_of_range_finrank_le_one
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_Pleft_isSymmetricProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_Pleft_ne_zero_of_nonzero_code_QECertTyped
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_Pleft_range_finrank_le_one_of_region_recoverable_QECertTyped


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1600000
namespace QEC.Bounds.BPTCommutingProjectorModel
private theorem qecertSecondCutPleftWitness79c2cc62db33d8d5
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier ≠ ⊥)
    (hM : M.RegionErasureRecoverable region)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    {n : Nat} [NeZero n]
    (W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    let A := M.fourFactorA region
    let H := component.1.restrictScalars Complex
    let W0 := W.restrictScalars Complex
    let N := isotypicLiftedMultiplicity.{0} n
    let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
    ∀ (U : Semantics.UnitaryTransport H (Semantics.CompositeSystem W0 N))
      (Pleft : Semantics.Operator (Semantics.CompositeSystem A W0))
      (Qright : Semantics.Operator (Semantics.CompositeSystem N CD)),
      M.secondCutCodeLift region * M.secondCutSectorLift region component =
          M.secondCutCodeLift region →
      (unitaryLTensor A U).conjOperator
          (overlapProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) component) =
          rightTensorExtensionAfterLeft A W0 N Pleft →
      (unitaryRTensor U CD).conjOperator
          (overlapRightProjectorOnIsotypicComponent
            (M.fourFactorProjectorABLocal region) (M.secondCutProjectorBbarM region) component) =
          leftTensorExtensionBeforeRight W0 N CD Qright →
      ∃ phi : Semantics.CompositeSystem A W0,
        ‖phi‖ = 1 ∧
        Pleft = (InnerProductSpace.rankOne Complex phi phi).toLinearMap := by
  intro A H W0 N CD U Pleft Qright hactive hleft hright
  exact isSymmetricProjection_eq_rankOne_of_ne_zero_of_range_finrank_le_one Pleft
    (M.secondCut_Pleft_isSymmetricProjection region component W U Pleft hleft)
    (M.secondCut_Pleft_ne_zero_of_nonzero_code_QECertTyped
      region hcode component W U Pleft Qright hactive hleft hright)
    (M.secondCut_Pleft_range_finrank_le_one_of_region_recoverable_QECertTyped
      region hcode hM component W U Pleft Qright hactive hleft hright)

theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.secondCut_Pleft_eq_rankOne_of_region_recoverable_QECertTypedStatement.{v} :=
  @qecertSecondCutPleftWitness79c2cc62db33d8d5

end QEC.Bounds.BPTCommutingProjectorModel
