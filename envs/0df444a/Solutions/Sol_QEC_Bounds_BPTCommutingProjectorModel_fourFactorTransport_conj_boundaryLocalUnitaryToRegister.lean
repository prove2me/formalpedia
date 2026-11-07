-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_boundaryLocalUnitaryToRegister
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:47:44.468966+00:00
-- url     : https://prove2.me/submissions/e51a6725-10f5-4197-92b3-12a2edc1024f

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryGlobalToFourFactorTransport_eq_fourFactorTransport
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryGlobalToFourFactorTransport_conj_boundaryLocalUnitaryToRegister

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
    (M.fourFactorTransport region).conjOperator
        (M.boundaryLocalUnitaryToRegister region U).toLinearEquiv.toLinearMap =
      M.fourFactorExtendBC region
        ((M.boundarySelectedToBCTransport region).conjOperator U.toLinearEquiv.toLinearMap) := by
  rw [← M.boundaryGlobalToFourFactorTransport_eq_fourFactorTransport region]
  exact M.boundaryGlobalToFourFactorTransport_conj_boundaryLocalUnitaryToRegister region U
end QEC.Bounds.BPTCommutingProjectorModel
