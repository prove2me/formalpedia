-- Prove2me | solution 1 for SNumbers.approximationNumber_zero_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:28:28.31707+00:00
-- url     : https://prove2.me/submissions/1e52ad8c-e957-4fea-90d2-cc9c4c71f847

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_SNumbers_approximationSet_zero
public import Theorems.Thm_ContinuousLinearMap_rank_zero
attribute [local simp] ContinuousLinearMap.rank_zero



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) :
    approximationNumber S 0 = ‖S‖ := by
  simp [approximationNumber, approximationSet_zero]
end SNumbers
