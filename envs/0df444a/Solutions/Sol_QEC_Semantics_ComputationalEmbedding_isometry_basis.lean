-- Prove2me | solution 1 for QEC.Semantics.ComputationalEmbedding.isometry_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:00:09.556757+00:00
-- url     : https://prove2.me/submissions/0050502b-36f8-434e-b459-8d1e254d51f3

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_ComputationalEmbedding
import Theorems.Thm_QEC_Semantics_ComputationalEmbedding_linearMap_basis

set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.ComputationalEmbedding
open scoped BigOperators
universe u v w
variable {A : Type u} {B : Type v} {C : Type w}
variable [Fintype A] [Fintype B] [Fintype C]
namespace QEC.Semantics.ComputationalEmbedding
theorem _root_.solution (e : A ↪ B) (a : A) :
    isometry e (EuclideanSpace.basisFun A Complex a) = EuclideanSpace.basisFun B Complex (e a) :=
  linearMap_basis e a
end QEC.Semantics.ComputationalEmbedding
