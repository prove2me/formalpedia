-- Prove2me | solution 1 for SNumbers.additive_gelfandNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:22:26.413805+00:00
-- url     : https://prove2.me/submissions/8d6f09ed-5502-424e-9a53-0c99118b4580

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
public import Theorems.Thm_SNumbers_gelfandNumber_additive

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
theorem _root_.solution :
    Additive (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => gelfandNumber S n) :=
  fun S T n m => gelfandNumber_additive S T n m
end SNumbers
