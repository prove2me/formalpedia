-- Prove2me | solution 1 for QEC.Semantics.ComputationalTensor.tripleTransport_tmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:44:00.824008+00:00
-- url     : https://prove2.me/submissions/8e2d8279-5e19-4653-bde4-ddac9de4d0dd

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_ComputationalTensor
import Theorems.Thm_QEC_Semantics_ComputationalTensor_tripleTransport_basis
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
theorem _root_.solution (x y z : EuclideanSpace Complex A) (a : A × A × A) :
    tripleTransport A (x ⊗ₜ[Complex] (y ⊗ₜ[Complex] z)) a = x a.1 * y a.2.1 * z a.2.2 := by
  calc
    _ = inner Complex (EuclideanSpace.basisFun _ Complex a)
        (tripleTransport A (x ⊗ₜ[Complex] (y ⊗ₜ[Complex] z))) :=
      (EuclideanSpace.basisFun_inner _ _ _ _).symm
    _ = inner Complex (tripleBasis A a) (x ⊗ₜ[Complex] (y ⊗ₜ[Complex] z)) := by
      rw [← tripleTransport_basis, (tripleTransport A).map_inner]
    _ = _ := by
      simp only [tripleBasis, OrthonormalBasis.tensorProduct_apply', TensorProduct.inner_tmul,
        EuclideanSpace.basisFun_inner]
      ring
end QEC.Semantics.ComputationalTensor
