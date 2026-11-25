-- Prove2me | solution 1 for SVD.isApproximable_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:18:32.548121+00:00
-- url     : https://prove2.me/submissions/ebd3b084-cc3e-4080-b87f-70ee263df77d

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_AddOns_Approximable
public import Theorems.Thm_SVD_IsApproximable_of_rank_le
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
theorem _root_.solution : IsApproximable (0 : X →L[𝕜] Y) :=
  IsApproximable.of_rank_le (N := 0) (by simp)
end SVD
