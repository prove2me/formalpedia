-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.projectorBC_mul_CD_supportedOnRegister
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:03:24.919621+00:00
-- url     : https://prove2.me/submissions/7d62ef78-40e1-47c8-b7ca-c77c1f7c7c47

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
    (M.regionSubsystem (M.boundary region ∪ regionᶜ)).OperatorSupportedOnRegister
      (M.projectorBC region * M.projectorCD region) :=
  M.operatorSupportedOnRegister_mul_union (M.boundary region) regionᶜ
    (M.projectorBC_supportedOnRegister_boundary region)
    (M.projectorCD_supportedOnRegister_complement region)
end QEC.Bounds.BPTCommutingProjectorModel
