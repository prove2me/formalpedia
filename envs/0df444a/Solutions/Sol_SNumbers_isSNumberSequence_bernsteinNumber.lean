-- Prove2me | solution 1 for SNumbers.isSNumberSequence_bernsteinNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:00:38.887404+00:00
-- url     : https://prove2.me/submissions/c391ec28-768a-466a-a9fa-71384a29bad3

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein
public import Theorems.Thm_SNumbers_bernsteinNumber_nonneg
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_bernsteinNumber_antitone
public import Theorems.Thm_SNumbers_bernsteinNumber_add_le
public import Theorems.Thm_SNumbers_bernsteinNumber_eq_zero_of_rank_le
public import Theorems.Thm_SNumbers_bernsteinNumber_id_euclidean
public import Theorems.Thm_SNumbers_bernsteinNumber_comp_comp_le
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_Additive_subadditive
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] Submodule.liftQL_mkQL


attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm

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
        (fun {_X _Y} _ _ _ _ S n => bernsteinNumber S n) where
  nonneg := fun S n => bernsteinNumber_nonneg S n
  norm_at_zero := fun S => bernsteinNumber_zero_eq_norm S
  antitone := fun S n => bernsteinNumber_antitone S n
  subadditive := fun S T n => bernsteinNumber_add_le S T n
  ideal := fun A S B n => bernsteinNumber_comp_comp_le A S B n
  vanishes_on_low_rank := fun _ _ h => bernsteinNumber_eq_zero_of_rank_le h
  normalised_at_id := fun n => bernsteinNumber_id_euclidean n
end SNumbers
