-- Prove2me | solution 1 for SNumbers.deviationFromRestriction_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:27:47.421805+00:00
-- url     : https://prove2.me/submissions/39fac962-4cf2-4769-b679-a437d3008a58

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand

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
theorem _root_.solution (S T : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    deviationFromRestriction (S + T) M ≤
      deviationFromRestriction S M + deviationFromRestriction T M := by
  unfold deviationFromRestriction
  rw [ContinuousLinearMap.add_comp]
  exact norm_add_le _ _
end SNumbers
