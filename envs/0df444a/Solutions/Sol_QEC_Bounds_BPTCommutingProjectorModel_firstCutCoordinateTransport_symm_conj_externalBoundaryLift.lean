-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_symm_conj_externalBoundaryLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:06:21.424304+00:00
-- url     : https://prove2.me/submissions/02721570-27e6-4112-95ff-87579d0b7edd

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_externalBoundaryLift
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCoordinateTransport_conj_externalBoundarySectorLift

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (Z : Semantics.Operator (M.fourFactorC region)) :
    (M.firstCutCoordinateTransport region).symm.conjOperator
      ((M.fourFactorTransport region).conjOperator
        ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
          ((M.fourFactorCCoordinateRelabel region).symm.conjOperator Z))) =
      overlapLiftLeft (C := M.fourFactorD region)
        (TensorProduct.map
          (1 : Semantics.Operator
            (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) Z) := by
  let U := M.firstCutCoordinateTransport region
  let sectorLift := overlapLiftLeft (C := M.fourFactorD region)
    (TensorProduct.map
      (1 : Semantics.Operator
        (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) Z)
  have hfour := M.fourFactorTransport_conj_externalBoundaryLift region Z
  have hfirst := M.firstCutCoordinateTransport_conj_externalBoundarySectorLift region Z
  calc
    U.symm.conjOperator
        ((M.fourFactorTransport region).conjOperator
          ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
            ((M.fourFactorCCoordinateRelabel region).symm.conjOperator Z))) =
        U.symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
            (TensorProduct.map (1 : Semantics.Operator (M.fourFactorB region))
              (TensorProduct.map Z (1 : Semantics.Operator (M.fourFactorD region))))) :=
      congrArg U.symm.conjOperator hfour
    _ = U.symm.conjOperator (U.conjOperator sectorLift) := by
      exact congrArg U.symm.conjOperator hfirst.symm
    _ = sectorLift := U.symm_conjOperator_conjOperator sectorLift
end QEC.Bounds.BPTCommutingProjectorModel
