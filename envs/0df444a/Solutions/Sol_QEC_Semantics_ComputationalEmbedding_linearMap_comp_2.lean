-- Prove2me | solution 2 for QEC.Semantics.ComputationalEmbedding.linearMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:00:10.559207+00:00
-- url     : https://prove2.me/submissions/f66d2aef-d94d-433d-9140-7c1784b1c042

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_ComputationalEmbedding
import Theorems.Thm_QEC_Semantics_ComputationalEmbedding_linearMap_basis
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
theorem _root_.solution (e : A ↪ B) (f : B ↪ C) :
    linearMap (e.trans f) = (linearMap f).comp (linearMap e) := by
  apply (EuclideanSpace.basisFun A Complex).toBasis.ext
  intro a
  change linearMap (e.trans f) (EuclideanSpace.basisFun A Complex a) =
    linearMap f (linearMap e (EuclideanSpace.basisFun A Complex a))
  simp only [linearMap_basis, Function.Embedding.trans_apply]
end QEC.Semantics.ComputationalEmbedding
