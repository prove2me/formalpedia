-- Prove2me | solution 1 for QEC.Distillation.threeWordTransport_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:06:59.605846+00:00
-- url     : https://prove2.me/submissions/14b8763f-0d43-454d-9d2b-640cf48b9c23

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Semantics_Core_ComputationalTensor
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_TensorRegister

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
open Semantics
open scoped TensorProduct BigOperators
variable (F J K : Type) [Fintype F] [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]
namespace QEC.Distillation
theorem _root_.solution (a : (J → F) × (J → F) × (J → F)) :
    threeWordTransport F J (EuclideanSpace.basisFun _ Complex a) =
      EuclideanSpace.basisFun _ Complex (threeWordEquiv F J a) :=
  OrthonormalBasis.equiv_apply_basis _ _ _ _
end QEC.Distillation
