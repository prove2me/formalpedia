-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_internalBoundaryLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:47:34.583765+00:00
-- url     : https://prove2.me/submissions/f473cbce-9a10-4921-8681-3aef2a61cf75

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryGlobalToFourFactorTransport_eq_fourFactorTransport
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryGlobalToFourFactorTransport_conj_extendLocalToRegister
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundarySelectedToBCTransport_conj_internalBoundaryLift
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundary_eq_internal_union_external
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_conj_tensorMap
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryLTensor_conj_tensorMap_left
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryTransport_ext


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
    (M.fourFactorTransport region).conjOperator
      ((M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
        ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z)) =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map Z
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
            (1 : Semantics.Operator (M.fourFactorD region)))) := by
  let B := M.regionSubsystem (M.internalBoundary region)
  let BC := M.regionSubsystem (M.boundary region)
  have hBBC : B.selected ⊆ BC.selected := by
    intro site hsite
    change site ∈ M.boundary region
    rw [M.boundary_eq_internal_union_external region]
    exact Finset.mem_union_left _ hsite
  let Zx : Semantics.Operator L.Register :=
    B.extendLocalToRegister ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z)
  change (M.fourFactorTransport region).conjOperator Zx =
      TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map Z
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
            (1 : Semantics.Operator (M.fourFactorD region))))
  calc
    (M.fourFactorTransport region).conjOperator Zx =
        (M.boundaryGlobalToFourFactorTransport region).conjOperator Zx := by
      exact congrArg (fun transport => transport.conjOperator Zx)
        (M.boundaryGlobalToFourFactorTransport_eq_fourFactorTransport region).symm
    _ = (M.boundaryGlobalToFourFactorTransport region).conjOperator
        (BC.extendLocalToRegister
          (liftLocalToLarger B BC hBBC
            ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z))) := by
      congr 1
      exact (extendLocalToRegister_liftLocalToLarger B BC hBBC
        ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z)).symm
    _ = M.fourFactorExtendBC region
        ((M.boundarySelectedToBCTransport region).conjOperator
          (liftLocalToLarger B BC hBBC
            ((M.fourFactorBCoordinateRelabel region).symm.conjOperator Z))) :=
      M.boundaryGlobalToFourFactorTransport_conj_extendLocalToRegister region _
    _ = M.fourFactorExtendBC region
        (TensorProduct.map Z (1 : Semantics.Operator (M.fourFactorC region))) := by
      rw [M.boundarySelectedToBCTransport_conj_internalBoundaryLift]
    _ = TensorProduct.map (1 : Semantics.Operator (M.fourFactorA region))
        (TensorProduct.map Z
          (TensorProduct.map (1 : Semantics.Operator (M.fourFactorC region))
            (1 : Semantics.Operator (M.fourFactorD region)))) := by
      have hmiddle : (M.fourFactorMiddleReassociate region).symm =
          unitaryLTensor (M.fourFactorA region)
            (tensorAssociatorUnitary (M.fourFactorB region) (M.fourFactorC region)
              (M.fourFactorD region)) := by
        apply unitaryTransport_ext
        rfl
      unfold fourFactorExtendBC
      rw [hmiddle, unitaryLTensor_conj_tensorMap_left]
      exact congrArg (fun operator => TensorProduct.map
        (1 : Semantics.Operator (M.fourFactorA region)) operator)
        (tensorAssociatorUnitary_conj_tensorMap Z
          (1 : Semantics.Operator (M.fourFactorC region))
          (1 : Semantics.Operator (M.fourFactorD region)))
end QEC.Bounds.BPTCommutingProjectorModel
