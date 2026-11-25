-- Prove2me | solution 1 for SNumbers.ratio_le_hilbertNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:05:58.582694+00:00
-- url     : https://prove2.me/submissions/5ae52ecb-11ff-478b-93c4-067203ba2467

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert
public import Theorems.Thm_SNumbers_hilbertSet_bddAbove

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
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) {A : L2 𝕜 →L[𝕜] X} {B : Y →L[𝕜] L2 𝕜}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    approximationNumber (B.comp (S.comp A)) n / (‖B‖ * ‖A‖) ≤ hilbertNumber S n :=
  le_csSup (hilbertSet_bddAbove S n) ⟨A, B, hA, hB, rfl⟩
end SNumbers
