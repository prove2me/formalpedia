-- Prove2me | solution 1 for SNumbers.hilbertNumber_zero_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:07:57.516595+00:00
-- url     : https://prove2.me/submissions/dbce475c-69c0-4d3c-98a1-1bd5658b7768

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert
public import Theorems.Thm_SNumbers_ratio_le_norm
public import Theorems.Thm_SNumbers_norm_le_hilbertNumber_zero

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y W Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) : hilbertNumber S 0 = ‖S‖ :=
  le_antisymm
    (Real.sSup_le (by rintro r ⟨A, B, hA, hB, rfl⟩; exact ratio_le_norm S 0 hA hB)
      (norm_nonneg S))
    (norm_le_hilbertNumber_zero S)
end SNumbers
