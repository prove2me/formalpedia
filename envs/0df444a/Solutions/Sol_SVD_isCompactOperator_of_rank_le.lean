-- Prove2me | solution 1 for SVD.isCompactOperator_of_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:59:43.072444+00:00
-- url     : https://prove2.me/submissions/a158490d-1d63-44c1-b7cc-8eca6b29c386

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_AddOns_Approximable
public import Theorems.Thm_SVD_IsApproximable_of_rank_le
public import Theorems.Thm_SVD_IsApproximable_isCompactOperator

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
variable [LocallyCompactSpace 𝕜] [CompleteSpace Y]
namespace SVD
theorem _root_.solution {S : X →L[𝕜] Y} {m : ℕ}
    (hS : S.rank ≤ (m : Cardinal)) : IsCompactOperator S :=
  (IsApproximable.of_rank_le hS).isCompactOperator
end SVD
