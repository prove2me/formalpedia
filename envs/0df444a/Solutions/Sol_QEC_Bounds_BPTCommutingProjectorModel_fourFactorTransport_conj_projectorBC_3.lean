-- Prove2me | solution 3 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_projectorBC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:47:32.590415+00:00
-- url     : https://prove2.me/submissions/f70d4f7d-1e36-4a3f-b7a1-f42e5980c35f

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryGlobalToFourFactorTransport_eq_fourFactorTransport
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryGlobalToFourFactorTransport_conj_extendLocalToRegister
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_extendLocalToRegister_projectorBCLocal

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
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.fourFactorTransport region).conjOperator (M.projectorBC region) =
      M.fourFactorExtendBC region (M.fourFactorProjectorBCLocal region) := by
  rw [← M.boundaryGlobalToFourFactorTransport_eq_fourFactorTransport region]
  rw [← M.extendLocalToRegister_projectorBCLocal region]
  rw [M.boundaryGlobalToFourFactorTransport_conj_extendLocalToRegister]
  rfl
end QEC.Bounds.BPTCommutingProjectorModel
