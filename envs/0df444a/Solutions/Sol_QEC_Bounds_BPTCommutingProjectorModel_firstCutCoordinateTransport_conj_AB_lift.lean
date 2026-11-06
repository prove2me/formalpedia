-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_AB_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:54:45.658598+00:00
-- url     : https://prove2.me/submissions/995b36fc-c6c5-40cb-8b6f-104f17f0fd62

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
    (P : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) :
    (M.firstCutCoordinateTransport region).conjOperator
      (TensorProduct.map
        (TensorProduct.map P (1 : Semantics.Operator (M.fourFactorC region)))
        (1 : Semantics.Operator (M.fourFactorD region))) =
      M.fourFactorExtendAB region P := by
  unfold firstCutCoordinateTransport
  rw [composeUnitaryTransport_conjOperator]
  rw [tensorAssociatorUnitary_conj_tensorMap]
  rw [TensorProduct.map_one]
  rfl
end QEC.Bounds.BPTCommutingProjectorModel
