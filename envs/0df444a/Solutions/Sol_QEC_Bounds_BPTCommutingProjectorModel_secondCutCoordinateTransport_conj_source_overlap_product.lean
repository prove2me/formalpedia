-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCutCoordinateTransport_conj_source_overlap_product
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:15:31.513926+00:00
-- url     : https://prove2.me/submissions/191dc5f8-d706-44e9-9d5d-7228843ac912
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCoordinateTransport_conj_overlapLiftLeft_AB
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCoordinateTransport_conj_overlapLiftRight_BbarM
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactor_codeProjector_eq_source_products
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.secondCutCoordinateTransport region).conjOperator
      (M.secondCutCodeLift region) =
      (M.fourFactorTransport region).conjOperator M.fullCodeProjector := by
  calc
    (M.secondCutCoordinateTransport region).conjOperator
        (M.secondCutCodeLift region) =
        (M.secondCutCoordinateTransport region).conjOperator
            (overlapLiftLeft
              (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
              (M.fourFactorProjectorABLocal region)) *
          (M.secondCutCoordinateTransport region).conjOperator
            (overlapLiftRight (A := M.fourFactorA region)
              (M.secondCutProjectorBbarM region)) := by
      unfold secondCutCodeLift
      exact Semantics.UnitaryTransport.conjOperator_mul _ _ _
    _ = M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) *
          (M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) *
            M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region)) := by
      rw [M.secondCutCoordinateTransport_conj_overlapLiftLeft_AB,
        M.secondCutCoordinateTransport_conj_overlapLiftRight_BbarM]
    _ = (M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) *
          M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region)) *
          M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) := by
      exact (mul_assoc
        (M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region))
        (M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region))
        (M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region))).symm
    _ = (M.fourFactorTransport region).conjOperator M.fullCodeProjector :=
      (M.fourFactor_codeProjector_eq_source_products region).symm
