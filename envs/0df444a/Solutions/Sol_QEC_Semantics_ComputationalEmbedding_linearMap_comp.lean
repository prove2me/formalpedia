-- Prove2me | solution 1 for QEC.Semantics.ComputationalEmbedding.linearMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:32:53.673204+00:00
-- url     : https://prove2.me/submissions/f3eb470f-a21d-4850-b51a-3d6d0e8c9607

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Core_ComputationalEmbedding
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.ComputationalEmbedding
open scoped BigOperators
universe u v w
variable {A : Type u} {B : Type v} {C : Type w}
variable [Fintype A] [Fintype B] [Fintype C]

theorem solution (e : A ↪ B) (f : B ↪ C) :
    linearMap (e.trans f) = (linearMap f).comp (linearMap e) := by
  classical
  ext psi c
  simp [linearMap, LinearMap.comp_apply, map_sum, EuclideanSpace.basisFun_apply]
