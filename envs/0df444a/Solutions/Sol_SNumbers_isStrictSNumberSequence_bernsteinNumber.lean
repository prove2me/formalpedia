-- Prove2me | solution 1 for SNumbers.isStrictSNumberSequence_bernsteinNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:04:33.87054+00:00
-- url     : https://prove2.me/submissions/759bae08-e296-4385-9500-bc42da89c2ed

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein
public import Theorems.Thm_SNumbers_bernsteinNumber_strict
public import Theorems.Thm_SNumbers_isSNumberSequence_bernsteinNumber

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
    IsStrictSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => bernsteinNumber S n) where
  toIsSNumberSequence := isSNumberSequence_bernsteinNumber
  strictly_normalised_at_id := fun n h => bernsteinNumber_strict n h
end SNumbers
