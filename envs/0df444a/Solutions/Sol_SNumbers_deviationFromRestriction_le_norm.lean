-- Prove2me | solution 1 for SNumbers.deviationFromRestriction_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:19:15.548865+00:00
-- url     : https://prove2.me/submissions/0ce3afa2-f293-4df0-932d-f9689bb077ae

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
theorem _root_.solution (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    deviationFromRestriction S M ≤ ‖S‖ := by
  unfold deviationFromRestriction
  calc ‖S.comp M.subtypeL‖
      ≤ ‖S‖ * ‖M.subtypeL‖ := opNorm_comp_le _ _
    _ ≤ ‖S‖ * 1 :=
        mul_le_mul_of_nonneg_left M.norm_subtypeL_le (norm_nonneg _)
    _ = ‖S‖ := mul_one _
end SNumbers
