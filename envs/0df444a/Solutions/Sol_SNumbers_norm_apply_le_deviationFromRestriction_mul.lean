-- Prove2me | solution 1 for SNumbers.norm_apply_le_deviationFromRestriction_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:56:31.330867+00:00
-- url     : https://prove2.me/submissions/df204eb8-1746-4956-9fd2-2e938b5c4b67

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
theorem _root_.solution (S : X →L[𝕜] Y) {M : Submodule 𝕜 X}
    {x : X} (hx : x ∈ M) : ‖S x‖ ≤ deviationFromRestriction S M * ‖x‖ :=
  (S.comp M.subtypeL).le_opNorm ⟨x, hx⟩
end SNumbers
