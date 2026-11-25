-- Prove2me | solution 1 for SNumbers.additive_approxFamily
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:18:16.372427+00:00
-- url     : https://prove2.me/submissions/0a22489b-a86c-43dc-8c9e-3a6dfd83af3c

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_SNumbers_approximationNumber_additive

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
variable [CompleteSpace 𝕜]
omit [CompleteSpace 𝕜]
namespace SNumbers
theorem _root_.solution : Additive (𝕜 := 𝕜) approxFamily :=
  fun S T n m => approximationNumber_additive S T n m
end SNumbers
