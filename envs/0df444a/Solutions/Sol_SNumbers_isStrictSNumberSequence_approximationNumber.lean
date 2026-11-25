-- Prove2me | solution 1 for SNumbers.isStrictSNumberSequence_approximationNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:55.637564+00:00
-- url     : https://prove2.me/submissions/8c715775-2d5e-4cdf-bd2f-b024bdea07be

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_SNumbers_approximationNumber_strict
public import Theorems.Thm_SNumbers_isSNumberSequence_approximationNumber

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
namespace SNumbers
theorem _root_.solution :
    IsStrictSNumberSequence (𝕜 := 𝕜) approxFamily where
  toIsSNumberSequence := isSNumberSequence_approximationNumber
  strictly_normalised_at_id := fun n h => approximationNumber_strict n h
end SNumbers
