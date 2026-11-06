-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.nestedFactorizationRight_conj_externalBoundaryLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:01:44.838402+00:00
-- url     : https://prove2.me/submissions/b16c415e-01c5-4135-a4c5-dd87591b8c48

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_selectedFactorization_conj_liftExternalBoundary
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_composeUnitaryTransport_conjOperator
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_registerFactorization_conj_extendLocalToRegister
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_conj_tensorMap
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryRTensor_conj_tensorMap_left
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
    (Z : Semantics.Operator (M.fourFactorC region)) :
    (nestedFactorizationRight (M.regionSubsystem region)
      (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
        intro site hsite
        exact Finset.mem_union_left _ hsite)).conjOperator
      ((M.regionSubsystem (M.externalBoundary region)).extendLocalToRegister
        ((M.fourFactorCCoordinateRelabel region).symm.conjOperator Z)) =
      TensorProduct.map (1 : Semantics.Operator (M.regionSubsystem region).selectedSystem)
        (TensorProduct.map Z (1 : Semantics.Operator
          (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem)) := by
  rw [← extendLocalToRegister_liftLocalToLarger
    (M.regionSubsystem (M.externalBoundary region))
    (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
      intro site hsite
      exact Finset.mem_union_right _ hsite)]
  have hright : nestedFactorizationRight (M.regionSubsystem region)
      (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
        intro site hsite
        exact Finset.mem_union_left _ hsite) =
      composeUnitaryTransport
        (composeUnitaryTransport
          (M.regionSubsystem (region ∪ M.externalBoundary region)).registerFactorization
          (unitaryRTensor
            ((M.regionSubsystem region).selectedFactorization
              (M.regionSubsystem (region ∪ M.externalBoundary region)) (by
                intro site hsite
                exact Finset.mem_union_left _ hsite))
            (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem))
        (tensorAssociatorUnitary
          (M.regionSubsystem region).selectedSystem
          (M.fourFactorC region)
          (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem) := by
    apply unitaryTransport_ext
    rfl
  rw [hright, composeUnitaryTransport_conjOperator,
    composeUnitaryTransport_conjOperator]
  rw [registerFactorization_conj_extendLocalToRegister]
  rw [unitaryRTensor_conj_tensorMap_left,
    M.selectedFactorization_conj_liftExternalBoundary region]
  exact tensorAssociatorUnitary_conj_tensorMap
    (1 : Semantics.Operator (M.regionSubsystem region).selectedSystem) Z
    (1 : Semantics.Operator
      (M.regionSubsystem (region ∪ M.externalBoundary region)).complementSystem)
end QEC.Bounds.BPTCommutingProjectorModel
