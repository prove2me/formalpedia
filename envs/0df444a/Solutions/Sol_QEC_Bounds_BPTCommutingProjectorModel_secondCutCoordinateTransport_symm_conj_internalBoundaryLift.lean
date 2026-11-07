-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCutCoordinateTransport_symm_conj_internalBoundaryLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:50:57.579022+00:00
-- url     : https://prove2.me/submissions/73fb133d-07ec-4fb0-8130-8e9d9f7d0d53

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCoordinateTransport_conj_internalBoundarySectorLift
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_internalBoundaryLift


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
    (Z : Semantics.Operator (M.fourFactorB region)) :
    (M.secondCutCoordinateTransport region).symm.conjOperator
      ((M.fourFactorTransport region).conjOperator
        ((M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
          ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z))) =
      overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region)) Z) := by
  let U := M.secondCutCoordinateTransport region
  let sectorLift := overlapLiftLeft
    (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
    (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region)) Z)
  have hfour := M.fourFactorTransport_conj_internalBoundaryLift region Z
  have hsecond := M.secondCutCoordinateTransport_conj_internalBoundarySectorLift region Z
  calc
    U.symm.conjOperator
        ((M.fourFactorTransport region).conjOperator
          ((M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
            ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z))) =
        U.symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
            (TensorProduct.map Z
              (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
                (1 : Semantics.Operator (M.fourFactorD region))))) :=
      congrArg U.symm.conjOperator hfour
    _ = U.symm.conjOperator (U.conjOperator sectorLift) := by
      exact congrArg U.symm.conjOperator hsecond.symm
    _ = sectorLift := U.symm_conjOperator_conjOperator sectorLift
end QEC.Bounds.BPTCommutingProjectorModel
