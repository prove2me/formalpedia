-- Prove2me | solution 1 for QEC.Distillation.threeWordTransport_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:41:41.167677+00:00
-- url     : https://prove2.me/submissions/fe9e9cd2-0b1d-49d2-aa7a-434adc81d5e6

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Semantics_Core_ComputationalTensor
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_TensorRegister
import Theorems.Thm_QEC_Distillation_threeWordTransport_basis

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
open Semantics
open scoped TensorProduct BigOperators
variable (F J K : Type) [Fintype F] [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]
namespace QEC.Distillation
theorem _root_.solution
    (psi : EuclideanSpace Complex ((J → F) × (J → F) × (J → F)))
    (a : (J → F) × (J → F) × (J → F)) :
    threeWordTransport F J psi (threeWordEquiv F J a) = psi a := by
  calc
    _ = inner Complex (EuclideanSpace.basisFun _ Complex (threeWordEquiv F J a))
      (threeWordTransport F J psi) := (EuclideanSpace.basisFun_inner _ _ _ _).symm
    _ = inner Complex (EuclideanSpace.basisFun _ Complex a) psi := by
      rw [← threeWordTransport_basis, (threeWordTransport F J).map_inner]
    _ = _ := EuclideanSpace.basisFun_inner _ _ _ _
end QEC.Distillation
