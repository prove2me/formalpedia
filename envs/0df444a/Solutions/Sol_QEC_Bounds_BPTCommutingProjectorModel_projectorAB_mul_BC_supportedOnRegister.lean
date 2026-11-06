-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.projectorAB_mul_BC_supportedOnRegister
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:02:54.563149+00:00
-- url     : https://prove2.me/submissions/612c36e1-9155-4cca-9b75-7d96c8b31b83

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_operatorSupportedOnRegister_mul_union

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
    (M.regionSubsystem (region ∪ M.boundary region)).OperatorSupportedOnRegister
      (M.projectorAB region * M.projectorBC region) :=
  M.operatorSupportedOnRegister_mul_union region (M.boundary region)
    (M.projectorAB_supportedOnRegister_region region)
    (M.projectorBC_supportedOnRegister_boundary region)
end QEC.Bounds.BPTCommutingProjectorModel
