-- Prove2me | solution 1 for SNumbers.isSNumberSequence_approximationNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:41.661151+00:00
-- url     : https://prove2.me/submissions/435c4809-bb20-4387-a5f0-ea0f96086b21

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
public import Theorems.Thm_SNumbers_approximationNumber_nonneg
public import Theorems.Thm_SNumbers_approximationNumber_antitone
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_approximationNumber_eq_zero_of_rank_le
public import Theorems.Thm_SNumbers_approximationNumber_add_le
public import Theorems.Thm_SNumbers_approximationNumber_comp_comp_le
public import Theorems.Thm_SNumbers_approximationNumber_id_euclidean
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_Additive_subadditive
attribute [local simp] ContinuousLinearMap.rank_zero


attribute [local simp] SNumbers.approximationNumber_zero_eq_norm

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
    IsSNumberSequence (𝕜 := 𝕜) approxFamily where
  norm_at_zero := fun S => approximationNumber_zero_eq_norm S
  antitone := fun S n => approximationNumber_antitone S n
  nonneg := fun S n => approximationNumber_nonneg S n
  subadditive := fun S T n => approximationNumber_add_le S T n
  ideal := fun A S B n => approximationNumber_comp_comp_le A S B n
  vanishes_on_low_rank := fun _ _ h => approximationNumber_eq_zero_of_rank_le h
  normalised_at_id := fun n => approximationNumber_id_euclidean n
end SNumbers
