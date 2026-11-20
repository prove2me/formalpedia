-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_comp_activeRegionEmbeddingsCore_QECertTyped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T20:00:05.326521+00:00
-- url     : https://prove2.me/submissions/ad6ee292-3ded-4207-99ec-48cf38efca76

import Definitions.Def_QEC_Import_Typed_7da7743b7d086c85
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_SelectedEmbeddingCore
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_ComplementEmbeddingCore
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransportFromRegion_comp_activeRegionEmbeddingsCore_QECertTyped
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_eq_fourFactorTransportFromRegion


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
private noncomputable def qecertFourthEmbeddingProof7da7743b7d086c85
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (bcomponent : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (ccomponent : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    {nB nC : Nat} [NeZero nB] [NeZero nC]
    (WB : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region))
    (WC : Submodule (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport (bcomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WB.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nB)))
    (UC : Semantics.UnitaryTransport (ccomponent.1.restrictScalars Complex)
      (Semantics.CompositeSystem (WC.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} nC))) :
    (M.fourFactorTransport region).toLinearEquiv.toLinearMap.comp
        ((M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap.comp
          (TensorProduct.map
            (M.activeSelectedEmbeddingCore region bcomponent WB UB).toLinearMap
            (M.activeComplementEmbeddingCore region ccomponent WC UC).toLinearMap)) =
      (fourFactorJointBCSectorEmbedding (A := M.fourFactorA region)
        (D := M.fourFactorD region) (bcomponent.1.restrictScalars Complex)
        (ccomponent.1.restrictScalars Complex)).comp
        ((M.secondCutJointActiveBlockTransport
          region bcomponent ccomponent WB WC UB UC).symm.toLinearEquiv.toLinearMap.comp
          ((tensorAssociatorUnitary
            (Semantics.CompositeSystem (M.fourFactorA region) (WB.restrictScalars Complex))
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nB)
              (WC.restrictScalars Complex))
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
              (M.fourFactorD region))).toLinearEquiv.toLinearMap.comp
            (productBlockRegrouping (A := M.fourFactorA region)
              (W := WB.restrictScalars Complex) (N := isotypicLiftedMultiplicity.{0} nB)
              (X := WC.restrictScalars Complex)
              (D := Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
                (M.fourFactorD region))).symm.toLinearEquiv.toLinearMap)) := by
  have htransport :
      (M.fourFactorTransport region).toLinearEquiv.toLinearMap =
        (M.fourFactorTransportFromRegion region).toLinearEquiv.toLinearMap :=
    congrArg (fun T : Semantics.UnitaryTransport L.Register _ =>
      T.toLinearEquiv.toLinearMap)
      (M.fourFactorTransport_eq_fourFactorTransportFromRegion region)
  exact (congrArg
    (fun F => F.comp
      ((M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap.comp
        (TensorProduct.map
          (M.activeSelectedEmbeddingCore region bcomponent WB UB).toLinearMap
          (M.activeComplementEmbeddingCore region ccomponent WC UC).toLinearMap)))
    htransport).trans
      (M.fourFactorTransportFromRegion_comp_activeRegionEmbeddingsCore_QECertTyped
        region bcomponent ccomponent WB WC UB UC)

theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_comp_activeRegionEmbeddingsCore_QECertTypedStatement.{v} :=
  @qecertFourthEmbeddingProof7da7743b7d086c85

end QEC.Bounds.BPTCommutingProjectorModel
