-- Prove2me | solution 1 for SNumbers.multiplicative_kolmogorovNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:21:39.692199+00:00
-- url     : https://prove2.me/submissions/4d4d16c4-4bef-4764-9c96-9c2ac211c47d

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
public import Theorems.Thm_SNumbers_kolmogorovNumber_multiplicative

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
    Multiplicative (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => kolmogorovNumber S n) :=
  fun S T n m => kolmogorovNumber_multiplicative S T n m
end SNumbers
