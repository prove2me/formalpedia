-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.secondCutGlobalCoordinateTransport_conj_fullCodeProjector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:58:07.906204+00:00
-- url     : https://prove2.me/submissions/6b027252-68d2-4bf2-8b18-f84cfdee639a

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCoordinateTransport_conj_source_overlap_product
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_composeUnitaryTransport_conjOperator


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
    (M.secondCutGlobalCoordinateTransport region).conjOperator M.fullCodeProjector =
      M.secondCutCodeLift region := by
  change (composeUnitaryTransport (M.fourFactorTransport region)
    (M.secondCutCoordinateTransport region).symm).conjOperator M.fullCodeProjector =
      M.secondCutCodeLift region
  rw [composeUnitaryTransport_conjOperator]
  calc
    (M.secondCutCoordinateTransport region).symm.conjOperator
        ((M.fourFactorTransport region).conjOperator M.fullCodeProjector) =
        (M.secondCutCoordinateTransport region).symm.conjOperator
          ((M.secondCutCoordinateTransport region).conjOperator
            (M.secondCutCodeLift region)) := by
      exact congrArg (M.secondCutCoordinateTransport region).symm.conjOperator
        (M.secondCutCoordinateTransport_conj_source_overlap_product region).symm
    _ = M.secondCutCodeLift region :=
      (M.secondCutCoordinateTransport region).symm_conjOperator_conjOperator _
end QEC.Bounds.BPTCommutingProjectorModel
