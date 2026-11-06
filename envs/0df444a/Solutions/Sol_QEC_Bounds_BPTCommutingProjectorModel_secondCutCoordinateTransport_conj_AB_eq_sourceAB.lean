-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCutCoordinateTransport_conj_AB_eq_sourceAB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:58:41.553323+00:00
-- url     : https://prove2.me/submissions/a0c0d2c3-89b2-4be1-9151-da4bd220c6d8

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCoordinateTransport_conj_overlapLiftLeft_AB
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_projectorAB


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
    (M.secondCutCoordinateTransport region).conjOperator
      (overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
        (M.fourFactorProjectorABLocal region)) =
      (M.fourFactorTransport region).conjOperator (M.projectorAB region) := by
  calc
    (M.secondCutCoordinateTransport region).conjOperator
        (overlapLiftLeft
          (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
          (M.fourFactorProjectorABLocal region)) =
        M.fourFactorExtendAB region (M.fourFactorProjectorABLocal region) :=
      M.secondCutCoordinateTransport_conj_overlapLiftLeft_AB region _
    _ = (M.fourFactorTransport region).conjOperator (M.projectorAB region) :=
      (M.fourFactorTransport_conj_projectorAB region).symm
end QEC.Bounds.BPTCommutingProjectorModel
