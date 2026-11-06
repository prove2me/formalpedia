-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.firstCutCoordinateTransport_conj_overlapLiftRight_CD_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:25:07.364025+00:00
-- url     : https://prove2.me/submissions/9c0874e8-6838-4e18-8c18-22c03fd81a73

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
      (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))) :
    (M.firstCutCoordinateTransport region).conjOperator
      (overlapLiftRight
        (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)) P) =
      M.fourFactorExtendCD region P := by
  unfold firstCutCoordinateTransport overlapLiftRight fourFactorExtendCD
  rw [composeUnitaryTransport_conjOperator]
  rw [Semantics.UnitaryTransport.conjOperator_symm_conjOperator]
  rw [show (1 : Semantics.Operator
      (Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))) =
        TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
          (1 : Semantics.Operator (M.fourFactorB region)) by
        symm
        exact TensorProduct.map_one]
  exact tensorAssociatorUnitary_conj_tensorMap
    (1 : Semantics.Operator (M.fourFactorA region))
    (1 : Semantics.Operator (M.fourFactorB region)) P
end QEC.Bounds.BPTCommutingProjectorModel
