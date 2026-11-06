-- Prove2me | solution 1 for QEC.Semantics.ComputationalEmbedding.linearMap_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:16:27.172639+00:00
-- url     : https://prove2.me/submissions/741a22d5-93be-431f-b805-58e20c6e69a6

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_ComputationalEmbedding
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.ComputationalEmbedding
open scoped BigOperators
universe u v w
variable {A : Type u} {B : Type v} {C : Type w}
variable [Fintype A] [Fintype B] [Fintype C]
namespace QEC.Semantics.ComputationalEmbedding
theorem _root_.solution (e : A ↪ B) (a : A) :
    linearMap e (EuclideanSpace.basisFun A Complex a) = EuclideanSpace.basisFun B Complex (e a) := by
  classical
  change (∑ b, EuclideanSpace.basisFun A Complex a b •
    EuclideanSpace.basisFun B Complex (e b)) = _
  simp [EuclideanSpace.basisFun_apply]
end QEC.Semantics.ComputationalEmbedding
