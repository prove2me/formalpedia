-- Prove2me | solution 1 for SNumbers.hilbertNumber_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:53:31.166515+00:00
-- url     : https://prove2.me/submissions/6fa0b9fb-a49f-4a2b-a73c-aed64abe5e0f

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert
public import Theorems.Thm_SNumbers_approximationNumber_nonneg


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
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) : 0 ≤ hilbertNumber S n :=
  Real.sSup_nonneg <| by
    rintro r ⟨A, B, hA, hB, rfl⟩
    exact div_nonneg (approximationNumber_nonneg _ _) (by positivity)
end SNumbers
