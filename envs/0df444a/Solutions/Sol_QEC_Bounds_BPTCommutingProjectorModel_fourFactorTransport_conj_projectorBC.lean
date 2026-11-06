-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_projectorBC
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:12:09.098033+00:00
-- url     : https://prove2.me/submissions/d5801868-0a48-4cd8-ac9b-54e1bac8db3a

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryGlobalToFourFactorTransport_eq_fourFactorTransport
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_extendLocalToRegister_projectorBCLocal
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryGlobalToFourFactorTransport_conj_extendLocalToRegister
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.fourFactorTransport region).conjOperator (M.projectorBC region) =
      M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) := by
  rw [← M.boundaryGlobalToFourFactorTransport_eq_fourFactorTransport region]
  rw [← M.extendLocalToRegister_projectorBCLocal region]
  rw [M.boundaryGlobalToFourFactorTransport_conj_extendLocalToRegister]
  rfl
