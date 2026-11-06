-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.boundarySelectedToBCTransport_conj_internalBoundaryLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:55:33.21459+00:00
-- url     : https://prove2.me/submissions/1fa4e889-0882-4a62-b27f-72d3f5cfb533

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundary_eq_internal_union_external
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_composeUnitaryTransport_conjOperator
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryLTensor_conj_tensorMap_right
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryRTensor_conj_tensorMap_left


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
    (M.boundarySelectedToBCTransport region).conjOperator
      (liftLocalToLarger (M.regionSubsystem (M.internalBoundary region))
        (M.regionSubsystem (M.boundary region)) (by
          intro site hsite
          rw [M.boundary_eq_internal_union_external region]
          exact Finset.mem_union_left _ hsite)
        ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z)) =
      TensorProduct.map Z (1 : Semantics.Operator (M.fourFactorC region)) := by
  let B := M.regionSubsystem (M.internalBoundary region)
  let BC := M.regionSubsystem (M.boundary region)
  have hBBC : B.selected ⊆ BC.selected := by
    intro site hsite
    change site ∈ M.boundary region
    rw [M.boundary_eq_internal_union_external region]
    exact Finset.mem_union_left _ hsite
  change (M.boundarySelectedToBCTransport region).conjOperator
      (liftLocalToLarger B BC hBBC
        ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z)) =
      TensorProduct.map Z (1 : Semantics.Operator (M.fourFactorC region))
  unfold boundarySelectedToBCTransport
  rw [composeUnitaryTransport_conjOperator, composeUnitaryTransport_conjOperator]
  rw [liftLocalToLarger, Semantics.UnitaryTransport.conjOperator_symm_conjOperator]
  rw [unitaryRTensor_conj_tensorMap_left]
  rw [(M.fourFactorBCoordinateRelabel region).conjOperator_symm_conjOperator]
  rw [unitaryLTensor_conj_tensorMap_right]
end QEC.Bounds.BPTCommutingProjectorModel
