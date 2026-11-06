-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_CD_eq_sourceCD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:01:39.362121+00:00
-- url     : https://prove2.me/submissions/727db7eb-87e4-4110-913d-a60531ea7de3

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_conj_projectorCD
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
      (overlapLiftRight
        (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
        (M.fourFactorProjectorCDLocal region)) =
      (M.fourFactorTransport region).conjOperator (M.projectorCD region) := by
  calc
    (M.firstCutCoordinateTransport region).conjOperator
        (overlapLiftRight
          (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
          (M.fourFactorProjectorCDLocal region)) =
        M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) :=
      M.firstCutCoordinateTransport_conj_overlapLiftRight_CD_lift region
        (M.fourFactorProjectorCDLocal region)
    _ = (M.fourFactorTransport region).conjOperator (M.projectorCD region) :=
      (M.fourFactorTransport_conj_projectorCD region).symm
end QEC.Bounds.BPTCommutingProjectorModel
