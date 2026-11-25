-- Prove2me | solution 1 for SVD.IsApproximable.comp_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:19:03.481817+00:00
-- url     : https://prove2.me/submissions/54f03907-b455-447c-b490-d5d5a6c504da

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_AddOns_Approximable
public import Theorems.Thm_SVD_IsApproximable_comp_comp
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open Filter Topology
open SVD
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SVD
namespace IsApproximable
theorem _root_.solution {S : X →L[𝕜] Y}
    (A : W →L[𝕜] X) (hS : IsApproximable S) :
    IsApproximable (S.comp A) := by
  -- `S.comp A = id_Y.comp (S.comp A)`, so this is a special case.
  have h := hS.comp_comp A (ContinuousLinearMap.id 𝕜 Y)
  simpa using h
end IsApproximable
end SVD
