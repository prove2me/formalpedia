-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_externalBoundarySectorLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:55:51.314176+00:00
-- url     : https://prove2.me/submissions/b9792e1c-0c0e-4102-9355-cf1582c9c416

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_composeUnitaryTransport_conjOperator
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_conj_tensorMap


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
    (M.firstCutCoordinateTransport region).conjOperator
      (overlapLiftLeft (C := M.fourFactorD region)
        (TensorProduct.map
          (1 : Semantics.Operator
            (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) Z)) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map (1 : Semantics.Operator (M.fourFactorB region))
          (TensorProduct.map Z (1 : Semantics.Operator (M.fourFactorD region))) ) := by
  unfold firstCutCoordinateTransport overlapLiftLeft
  rw [composeUnitaryTransport_conjOperator]
  rw [tensorAssociatorUnitary_conj_tensorMap]
  rw [show (1 : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) =
        TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
          (1 : Semantics.Operator (M.fourFactorB region)) by
        symm
        exact TensorProduct.map_one]
  exact tensorAssociatorUnitary_conj_tensorMap
    (1 : Semantics.Operator (M.fourFactorA region))
    (1 : Semantics.Operator (M.fourFactorB region))
    (TensorProduct.map Z (1 : Semantics.Operator (M.fourFactorD region)))
end QEC.Bounds.BPTCommutingProjectorModel
