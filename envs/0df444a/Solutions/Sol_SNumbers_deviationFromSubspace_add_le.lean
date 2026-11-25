-- Prove2me | solution 1 for SNumbers.deviationFromSubspace_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:29:13.564292+00:00
-- url     : https://prove2.me/submissions/499d0866-b3a0-4297-9290-e9ccd10092fe

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov

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
theorem _root_.solution (S T : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    deviationFromSubspace (S + T) V ≤
      deviationFromSubspace S V + deviationFromSubspace T V := by
  unfold deviationFromSubspace
  rw [ContinuousLinearMap.comp_add]
  exact norm_add_le _ _
end SNumbers
