-- Prove2me | solution 1 for SNumbers.additive_kolmogorovNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:20:35.357039+00:00
-- url     : https://prove2.me/submissions/1f2bdb88-0474-4ae5-ab6f-c49e4c0de393

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
public import Theorems.Thm_SNumbers_kolmogorovNumber_additive

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
theorem _root_.solution :
    Additive (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => kolmogorovNumber S n) :=
  fun S T n m => kolmogorovNumber_additive S T n m
end SNumbers
