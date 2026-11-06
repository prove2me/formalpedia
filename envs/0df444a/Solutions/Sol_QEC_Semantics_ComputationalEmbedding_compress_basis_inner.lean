-- Prove2me | solution 1 for QEC.Semantics.ComputationalEmbedding.compress_basis_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:00:13.387183+00:00
-- url     : https://prove2.me/submissions/5477ee65-71c3-43c0-b1f2-a3d587c7f2a0

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_ComputationalEmbedding
import Theorems.Thm_QEC_Semantics_ComputationalEmbedding_linearMap_basis
import Theorems.Thm_QEC_Semantics_ComputationalEmbedding_compress_inner

set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.ComputationalEmbedding
open scoped BigOperators
universe u v w
variable {A : Type u} {B : Type v} {C : Type w}
variable [Fintype A] [Fintype B] [Fintype C]
namespace QEC.Semantics.ComputationalEmbedding
theorem _root_.solution (e : A ↪ B) (E : Operator (EuclideanSpace Complex B))
    (a b : A) :
    inner Complex (EuclideanSpace.basisFun A Complex a)
        (compress e E (EuclideanSpace.basisFun A Complex b)) =
      inner Complex (EuclideanSpace.basisFun B Complex (e a))
        (E (EuclideanSpace.basisFun B Complex (e b))) := by
  rw [compress_inner, linearMap_basis, linearMap_basis]
end QEC.Semantics.ComputationalEmbedding
