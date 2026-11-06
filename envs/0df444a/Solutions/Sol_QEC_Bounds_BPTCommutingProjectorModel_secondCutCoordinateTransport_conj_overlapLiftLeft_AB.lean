-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCutCoordinateTransport_conj_overlapLiftLeft_AB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:17:45.311222+00:00
-- url     : https://prove2.me/submissions/813acf34-f0b8-4d9b-af2e-86750998982b

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection

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
    (P : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) :
    (M.secondCutCoordinateTransport region).conjOperator
      (overlapLiftLeft
        (C := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)) P) =
      M.fourFactorExtendAB region P := by
  unfold secondCutCoordinateTransport overlapLiftLeft fourFactorExtendAB
  rfl
end QEC.Bounds.BPTCommutingProjectorModel
