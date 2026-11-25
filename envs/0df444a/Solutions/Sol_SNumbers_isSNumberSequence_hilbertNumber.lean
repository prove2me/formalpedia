-- Prove2me | solution 1 for SNumbers.isSNumberSequence_hilbertNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:10:21.867698+00:00
-- url     : https://prove2.me/submissions/11dff87e-c93b-4323-8501-b6202faa988e

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert
public import Theorems.Thm_SNumbers_hilbertNumber_nonneg
public import Theorems.Thm_SNumbers_hilbertNumber_antitone
public import Theorems.Thm_SNumbers_hilbertNumber_comp_comp_le
public import Theorems.Thm_SNumbers_hilbertNumber_eq_zero_of_rank_le
public import Theorems.Thm_SNumbers_hilbertNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_hilbertNumber_le_norm
public import Theorems.Thm_SNumbers_hilbertNumber_add_le
public import Theorems.Thm_SNumbers_one_le_hilbertNumber_id
public import Theorems.Thm_SNumbers_Additive_subadditive


set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y W Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
theorem _root_.solution :
    IsSNumberSequence (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => hilbertNumber S n) where
  nonneg := fun S n => hilbertNumber_nonneg S n
  norm_at_zero := fun S => hilbertNumber_zero_eq_norm S
  antitone := fun S n => hilbertNumber_antitone S n
  subadditive := fun S T n => hilbertNumber_add_le S T n
  ideal := fun A S B n => hilbertNumber_comp_comp_le A S B n
  vanishes_on_low_rank := fun _ _ h => hilbertNumber_eq_zero_of_rank_le h
  normalised_at_id := fun n =>
    le_antisymm ((hilbertNumber_le_norm _ n).trans norm_id_le) (one_le_hilbertNumber_id n)
end SNumbers
