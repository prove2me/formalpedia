-- Prove2me | solution 1 for SNumbers.additive_hilbertNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:24:25.637121+00:00
-- url     : https://prove2.me/submissions/5e0bbe6b-4931-459e-9176-8f2e8ac051b7

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert
public import Theorems.Thm_SNumbers_hilbertNumber_additive

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
theorem _root_.solution :
    Additive (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => hilbertNumber S n) :=
  fun S T n m => hilbertNumber_additive S T n m
end SNumbers
