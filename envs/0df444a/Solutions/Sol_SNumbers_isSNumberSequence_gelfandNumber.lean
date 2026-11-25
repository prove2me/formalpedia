-- Prove2me | solution 1 for SNumbers.isSNumberSequence_gelfandNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:01:49.635835+00:00
-- url     : https://prove2.me/submissions/a62c3f08-3a7b-45ea-b833-1b525d9451ae

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
public import Theorems.Thm_SNumbers_gelfandNumber_nonneg
public import Theorems.Thm_SNumbers_gelfandNumber_antitone
public import Theorems.Thm_SNumbers_gelfandNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_gelfandNumber_add_le
public import Theorems.Thm_SNumbers_gelfandNumber_comp_comp_le
public import Theorems.Thm_SNumbers_gelfandNumber_eq_zero_of_rank_le
public import Theorems.Thm_SNumbers_gelfandNumber_id_euclidean
public import Theorems.Thm_SNumbers_Additive_subadditive


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
    IsSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => gelfandNumber S n) where
  nonneg := fun S n => gelfandNumber_nonneg S n
  norm_at_zero := fun S => gelfandNumber_zero_eq_norm S
  antitone := fun S n => gelfandNumber_antitone S n
  subadditive := fun S T n => gelfandNumber_add_le S T n
  ideal := fun A S B n => gelfandNumber_comp_comp_le A S B n
  vanishes_on_low_rank := fun _ _ h => gelfandNumber_eq_zero_of_rank_le h
  normalised_at_id := fun n => gelfandNumber_id_euclidean n
end SNumbers
