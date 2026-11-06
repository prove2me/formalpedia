-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.boundaryGlobalToFourFactorTransport_conj_boundaryLocalUnitaryToRegister
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:01:17.668633+00:00
-- url     : https://prove2.me/submissions/1b30584a-83c4-47d7-9422-8b41869740da

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryGlobalToFourFactorTransport_conj_extendLocalToRegister
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_extendLocalUnitaryToRegister_toLinearMap_eq


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
    (U : Semantics.UnitaryTransport
      (M.regionSubsystem (M.boundary region)).selectedSystem
      (M.regionSubsystem (M.boundary region)).selectedSystem) :
    (M.boundaryGlobalToFourFactorTransport region).conjOperator
        (M.boundaryLocalUnitaryToRegister region U).toLinearEquiv.toLinearMap =
      M.fourFactorExtendBC region
        ((M.boundarySelectedToBCTransport region).conjOperator U.toLinearEquiv.toLinearMap) := by
  change (M.boundaryGlobalToFourFactorTransport region).conjOperator
      (extendLocalUnitaryToRegister L.localDimension
        (M.regionSubsystem (M.boundary region)) U).toLinearEquiv.toLinearMap = _
  rw [extendLocalUnitaryToRegister_toLinearMap_eq]
  exact M.boundaryGlobalToFourFactorTransport_conj_extendLocalToRegister region _
end QEC.Bounds.BPTCommutingProjectorModel
