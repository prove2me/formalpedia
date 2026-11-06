-- Prove2me | solution 1 for QEC.Semantics.ComputationalEmbedding.compress_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:43:52.725323+00:00
-- url     : https://prove2.me/submissions/638b35a6-7d33-48e8-8242-df5e8461f110

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_ComputationalEmbedding

set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.ComputationalEmbedding
open scoped BigOperators
universe u v w
variable {A : Type u} {B : Type v} {C : Type w}
variable [Fintype A] [Fintype B] [Fintype C]
namespace QEC.Semantics.ComputationalEmbedding
theorem _root_.solution (e : A ↪ B) (E : Operator (EuclideanSpace Complex B))
    (x y : EuclideanSpace Complex A) :
    inner Complex x (compress e E y) = inner Complex (linearMap e x) (E (linearMap e y)) := by
  change inner Complex x (LinearMap.adjoint (linearMap e) (E (linearMap e y))) = _
  rw [LinearMap.adjoint_inner_right]
end QEC.Semantics.ComputationalEmbedding
