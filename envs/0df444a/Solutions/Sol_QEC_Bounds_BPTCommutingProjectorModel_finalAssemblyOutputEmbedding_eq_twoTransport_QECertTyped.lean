-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyOutputEmbedding_eq_twoTransport_QECertTyped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:32:58.871181+00:00
-- url     : https://prove2.me/submissions/22788a0b-01c6-4560-b965-3c0d7678b511

import Definitions.Def_QEC_Import_Typed_0b743f271464ca59
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Coordinates
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyInputEmbedding_eq_outputEmbedding_QECertTyped
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssemblyInputEmbedding_eq_twoTransport_QECertTyped


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000
namespace QEC.Bounds.BPTCommutingProjectorModel
private noncomputable def qecertOutputTwoTransportCombined0b743f271464ca59
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
    M.finalAssemblyOutputEmbedding region bcomponent ccomponent WB WC UB UC =
      (M.fourFactorTransport region).toLinearEquiv.toLinearMap.comp
        ((M.regionSubsystem region).registerFactorization.symm.toLinearEquiv.toLinearMap.comp
          (TensorProduct.map
            (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
            (M.activeComplementEmbedding region ccomponent WC UC).toLinearMap)) := by
  exact (M.finalAssemblyInputEmbedding_eq_outputEmbedding_QECertTyped
    region bcomponent ccomponent WB WC UB UC).symm.trans
    (M.finalAssemblyInputEmbedding_eq_twoTransport_QECertTyped
      region bcomponent ccomponent WB WC UB UC).symm

theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyOutputEmbedding_eq_twoTransport_QECertTypedStatement.{v} :=
  @qecertOutputTwoTransportCombined0b743f271464ca59

end QEC.Bounds.BPTCommutingProjectorModel
