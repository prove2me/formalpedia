-- Prove2me | solution 1 for SNumbers.deviationFromRestriction_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:27:45.575815+00:00
-- url     : https://prove2.me/submissions/cfcfb048-44b8-40a1-a449-edf5b6da3230

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
public import Theorems.Thm_SNumbers_deviationFromRestriction_nonneg
public import Theorems.Thm_SNumbers_norm_apply_le_deviationFromRestriction_mul

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
theorem _root_.solution (S : X →L[𝕜] Y) {M M' : Submodule 𝕜 X} (h : M' ≤ M) :
    deviationFromRestriction S M' ≤ deviationFromRestriction S M := by
  refine opNorm_le_bound (S.comp M'.subtypeL) (deviationFromRestriction_nonneg S M)
    fun x => ?_
  exact norm_apply_le_deviationFromRestriction_mul S (h x.2)
end SNumbers
