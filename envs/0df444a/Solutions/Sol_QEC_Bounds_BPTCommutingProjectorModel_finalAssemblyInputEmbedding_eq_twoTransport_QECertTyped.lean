-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyInputEmbedding_eq_twoTransport_QECertTyped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T19:55:58.923378+00:00
-- url     : https://prove2.me/submissions/bc8615d2-9217-4ccd-ad77-88c094e46003

import Definitions.Def_QEC_Import_Typed_9c48142235645f69
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 4000000
namespace QEC.Bounds.BPTCommutingProjectorModel
private noncomputable def qecertTwoTransportProof9c48142235645f69
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
            (M.activeSelectedEmbedding region bcomponent WB UB).toLinearMap
            (M.activeComplementEmbedding region ccomponent WC UC).toLinearMap)) =
      M.finalAssemblyInputEmbedding region bcomponent ccomponent WB WC UB UC := by
  rfl

theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyInputEmbedding_eq_twoTransport_QECertTypedStatement.{v} :=
  @qecertTwoTransportProof9c48142235645f69

end QEC.Bounds.BPTCommutingProjectorModel
