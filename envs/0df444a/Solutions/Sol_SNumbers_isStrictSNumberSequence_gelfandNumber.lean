-- Prove2me | solution 1 for SNumbers.isStrictSNumberSequence_gelfandNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:54.716338+00:00
-- url     : https://prove2.me/submissions/ea79aae7-0209-46bd-bf59-fbc015181bbc

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
public import Theorems.Thm_SNumbers_gelfandNumber_strict
public import Theorems.Thm_SNumbers_isSNumberSequence_gelfandNumber

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
        (fun {_X _Y} _ _ _ _ S n => gelfandNumber S n) where
  toIsSNumberSequence := isSNumberSequence_gelfandNumber
  strictly_normalised_at_id := fun n h => gelfandNumber_strict n h
end SNumbers
