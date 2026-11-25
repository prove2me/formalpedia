-- Prove2me | solution 1 for SNumbers.L2Linf.idEmbed_two_infty_comp_idEmbed_infty_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:15:45.634833+00:00
-- url     : https://prove2.me/submissions/ae25bf5a-b0e7-4b34-95b7-843b38f0f8f7

module
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Operator.Prod
public import Definitions.Def_SNumbers_Examples_IdentityL2Linfty

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal ComplexConjugate
open ContinuousLinearMap
open SNumbers SNumbers.L2Linf
variable {𝕜 : Type u} [RCLike 𝕜]
namespace SNumbers.L2Linf
theorem _root_.solution (N : ℕ) :
    (idEmbed (𝕜 := 𝕜) (m := N) 2 ∞).comp (idEmbed ∞ 2) =
      ContinuousLinearMap.id 𝕜 (PiLp 2 (fun _ : Fin N => 𝕜)) := by
  refine ContinuousLinearMap.ext fun x => ?_
  rfl
end SNumbers.L2Linf
