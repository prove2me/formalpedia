-- Prove2me | solution 1 for QEC.Distillation.taggedTensorCube_basis_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:46:53.212675+00:00
-- url     : https://prove2.me/submissions/caa2a724-9e8f-45f8-966d-f756efa9f50d

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Semantics_Core_ComputationalTensor
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_TensorRegister
import Theorems.Thm_QEC_Distillation_threeWordTransport_basis
import Theorems.Thm_QEC_Distillation_threeWordTransport_apply
import Theorems.Thm_QEC_Semantics_ComputationalTensor_tripleMap_basis_apply


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
open Semantics
open scoped TensorProduct BigOperators
variable (F J K : Type) [Fintype F] [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]
namespace QEC.Distillation
theorem _root_.solution
    (f : ComputationalBasisRegister F J →ₗ[Complex] ComputationalBasisRegister F K)
    (u : TaggedThreeCopyRegisterLabel F J) (v : TaggedThreeCopyRegisterLabel F K) :
    taggedTensorCube F J K f (EuclideanSpace.basisFun _ Complex u) v =
      f (EuclideanSpace.basisFun _ Complex (extractBlock u .first)) (extractBlock v .first) *
        f (EuclideanSpace.basisFun _ Complex (extractBlock u .second)) (extractBlock v .second) *
        f (EuclideanSpace.basisFun _ Complex (extractBlock u .third)) (extractBlock v .third) := by
  let a := (threeWordEquiv F J).symm u
  let b := (threeWordEquiv F K).symm v
  have ha : (threeWordTransport F J).toLinearEquiv.symm (EuclideanSpace.basisFun _ Complex u) =
      EuclideanSpace.basisFun _ Complex a := by
    apply (threeWordTransport F J).toLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply, threeWordTransport_basis]
    rw [show threeWordEquiv F J a = u from (threeWordEquiv F J).apply_symm_apply u]
  change threeWordTransport F K (ComputationalTensor.tripleMap _ _ f
    ((threeWordTransport F J).toLinearEquiv.symm (EuclideanSpace.basisFun _ Complex u))) v = _
  rw [ha, ← (threeWordEquiv F K).apply_symm_apply v, threeWordTransport_apply]
  exact ComputationalTensor.tripleMap_basis_apply _ _ f a b
end QEC.Distillation
