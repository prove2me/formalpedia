-- Prove2me | solution 1 for SNumbers.isSNumberSequence_kolmogorovNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:29.146619+00:00
-- url     : https://prove2.me/submissions/c6b6b0dd-0284-4f28-8b38-d9bb9ccc397d

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
public import Theorems.Thm_SNumbers_kolmogorovNumber_nonneg
public import Theorems.Thm_SNumbers_kolmogorovNumber_antitone
public import Theorems.Thm_SNumbers_kolmogorovNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_kolmogorovNumber_add_le
public import Theorems.Thm_SNumbers_kolmogorovNumber_comp_comp_le
public import Theorems.Thm_SNumbers_kolmogorovNumber_eq_zero_of_rank_le
public import Theorems.Thm_SNumbers_kolmogorovNumber_id_euclidean
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
variable [CompleteSpace 𝕜]
namespace SNumbers
theorem _root_.solution :
    IsSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => kolmogorovNumber S n) where
  nonneg := fun S n => kolmogorovNumber_nonneg S n
  norm_at_zero := fun S => kolmogorovNumber_zero_eq_norm S
  antitone := fun S n => kolmogorovNumber_antitone S n
  subadditive := fun S T n => kolmogorovNumber_add_le S T n
  ideal := fun A S B n => kolmogorovNumber_comp_comp_le A S B n
  vanishes_on_low_rank := fun _ _ h => kolmogorovNumber_eq_zero_of_rank_le h
  normalised_at_id := fun n => kolmogorovNumber_id_euclidean n
end SNumbers
