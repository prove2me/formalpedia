-- Prove2me | solution 1 for QEC.Semantics.ComputationalTensor.tripleMap_basis_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:00:19.696057+00:00
-- url     : https://prove2.me/submissions/a3e2720b-e2fd-43f3-8f12-ec1e911f7aef

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_ComputationalTensor
import Theorems.Thm_QEC_Semantics_ComputationalTensor_tripleTransport_basis
import Theorems.Thm_QEC_Semantics_ComputationalTensor_tripleTransport_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.ComputationalTensor
open scoped TensorProduct
variable (A B : Type) [Fintype A] [Fintype B]
namespace QEC.Semantics.ComputationalTensor
theorem _root_.solution
    (f : EuclideanSpace Complex A →ₗ[Complex] EuclideanSpace Complex B)
    (a : A × A × A) (b : B × B × B) :
    tripleMap A B f (EuclideanSpace.basisFun _ Complex a) b =
      f (EuclideanSpace.basisFun _ Complex a.1) b.1 *
        f (EuclideanSpace.basisFun _ Complex a.2.1) b.2.1 *
        f (EuclideanSpace.basisFun _ Complex a.2.2) b.2.2 := by
  have hinv : (tripleTransport A).toLinearEquiv.symm (EuclideanSpace.basisFun _ Complex a) =
      tripleBasis A a := by
    apply (tripleTransport A).toLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply, tripleTransport_basis]
  change tripleTransport B (TensorProduct.map f (TensorProduct.map f f)
    ((tripleTransport A).toLinearEquiv.symm (EuclideanSpace.basisFun _ Complex a))) b = _
  rw [hinv]
  simp only [tripleBasis, OrthonormalBasis.tensorProduct_apply', TensorProduct.map_tmul]
  exact tripleTransport_tmul B _ _ _ b
end QEC.Semantics.ComputationalTensor
