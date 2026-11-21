-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCut_Pleft_range_finrank_le_one_of_region_recoverable_QECertTyped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:53:53.982095+00:00
-- url     : https://prove2.me/submissions/cf056bca-9cd7-4250-8c12-a424260db6c3

import Definitions.Def_QEC_Import_Typed_462f37e09c90bb92
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftPhysical
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_RankOne
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOne
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finrank_range_le_one_of_all_scalar_compression
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_Pleft_all_scalar_compression_of_region_recoverable_QECertTyped
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_Pleft_isSymmetricProjection


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
private theorem qecertSecondCutPleftRank462f37e09c90bb92
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
      Module.finrank Complex (LinearMap.range Pleft) ≤ 1 := by
  intro A H W0 N CD U Pleft Qright hactive hleft hright
  have hscalar : ∀ X : Semantics.Operator
      (Semantics.CompositeSystem A W0),
      ∃ scalar : Complex, Pleft * X * Pleft = scalar • Pleft := by
    exact M.secondCut_Pleft_all_scalar_compression_of_region_recoverable_QECertTyped
      region hcode hM component W U Pleft Qright hactive hleft hright
  exact finrank_range_le_one_of_all_scalar_compression
    (H := Semantics.CompositeSystem A W0)
    Pleft (M.secondCut_Pleft_isSymmetricProjection region component W U Pleft hleft) hscalar

theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.secondCut_Pleft_range_finrank_le_one_of_region_recoverable_QECertTypedStatement.{v} :=
  @qecertSecondCutPleftRank462f37e09c90bb92

end QEC.Bounds.BPTCommutingProjectorModel
