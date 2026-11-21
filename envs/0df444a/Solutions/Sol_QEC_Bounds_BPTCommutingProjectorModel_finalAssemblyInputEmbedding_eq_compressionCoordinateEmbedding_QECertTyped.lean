-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyInputEmbedding_eq_compressionCoordinateEmbedding_QECertTyped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:34:05.287824+00:00
-- url     : https://prove2.me/submissions/3f5bde11-2823-4d92-bda1-3b580dcb2525

import Definitions.Def_QEC_Import_Typed_c75aa81e047254c4
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_CompressionExteriorCoordinates

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
namespace QEC.Bounds.BPTCommutingProjectorModel
private theorem qecertCompressionFrontierc75aa81e047254c4
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
    M.finalAssemblyInputEmbedding region bcomponent ccomponent WB WC UB UC =
      (M.fourFactorTransport region).toLinearEquiv.toLinearMap.comp
        (M.finalAssemblyCompressionCoordinateEmbedding
          region bcomponent ccomponent WB WC UB UC) := by
  rfl

theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.finalAssemblyInputEmbedding_eq_compressionCoordinateEmbedding_QECertTypedStatement.{v} :=
  @qecertCompressionFrontierc75aa81e047254c4

end QEC.Bounds.BPTCommutingProjectorModel
