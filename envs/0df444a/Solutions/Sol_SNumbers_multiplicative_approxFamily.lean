-- Prove2me | solution 1 for SNumbers.multiplicative_approxFamily
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:18:26.766422+00:00
-- url     : https://prove2.me/submissions/e41857b2-d8ab-4729-8a31-d49eee6ea46d

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_SNumbers_approximationNumber_multiplicative

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
theorem _root_.solution : Multiplicative (𝕜 := 𝕜) approxFamily :=
  fun S T n m => approximationNumber_multiplicative S T n m
end SNumbers
