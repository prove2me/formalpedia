-- Prove2me | solution 1 for SNumbers.deviationFromSubspace_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:20:22.784524+00:00
-- url     : https://prove2.me/submissions/84881b38-33d1-4cff-8271-7e6892fcc566

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
public import Theorems.Thm_Submodule_norm_mkQL_le


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
theorem _root_.solution (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    deviationFromSubspace S V ≤ ‖S‖ := by
  unfold deviationFromSubspace
  calc ‖V.mkQL.comp S‖
      ≤ ‖V.mkQL‖ * ‖S‖ := opNorm_comp_le _ _
    _ ≤ 1 * ‖S‖ := mul_le_mul_of_nonneg_right V.norm_mkQL_le (norm_nonneg _)
    _ = ‖S‖ := one_mul _
end SNumbers
