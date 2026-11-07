-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_source_overlap_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:52:45.507965+00:00
-- url     : https://prove2.me/submissions/1e4977b2-29c6-4f30-9d94-de4aae4d5d78

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactor_codeProjector_eq_source_products
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCoordinateTransport_conj_overlapLiftLeft_firstCutProjectorMC
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCoordinateTransport_conj_overlapLiftRight_CD_lift

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
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutCoordinateTransport region).conjOperator
      (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region) *
        overlapLiftRight
          (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (M.fourFactorProjectorCDLocal region)) =
      (M.fourFactorTransport region).conjOperator M.fullCodeProjector := by
  calc
    (M.firstCutCoordinateTransport region).conjOperator
        (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region) *
          overlapLiftRight
            (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
            (M.fourFactorProjectorCDLocal region)) =
        (M.firstCutCoordinateTransport region).conjOperator
            (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region)) *
          (M.firstCutCoordinateTransport region).conjOperator
            (overlapLiftRight
              (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
              (M.fourFactorProjectorCDLocal region)) :=
      Semantics.UnitaryTransport.conjOperator_mul
        (M.firstCutCoordinateTransport region)
        (overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region))
        (overlapLiftRight
          (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (M.fourFactorProjectorCDLocal region))
    _ = (M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) *
          M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region)) *
          M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) := by
      rw [M.firstCutCoordinateTransport_conj_overlapLiftLeft_firstCutProjectorMC,
        M.firstCutCoordinateTransport_conj_overlapLiftRight_CD_lift]
    _ = (M.fourFactorTransport region).conjOperator M.fullCodeProjector :=
      (M.fourFactor_codeProjector_eq_source_products region).symm
end QEC.Bounds.BPTCommutingProjectorModel
