-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.boundaryLocalUnitaryToRegister_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:51:55.571078+00:00
-- url     : https://prove2.me/submissions/ab0d7626-188b-44d5-b6c5-9394d8991cc0

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
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
    M.UnitarySupportedOn (M.boundary region)
      (M.boundaryLocalUnitaryToRegister region U) := by
  refine ⟨U.toLinearEquiv.toLinearMap, ?_⟩
  exact extendLocalUnitaryToRegister_toLinearMap_eq L.localDimension
    (M.regionSubsystem (M.boundary region)) U
end QEC.Bounds.BPTCommutingProjectorModel
