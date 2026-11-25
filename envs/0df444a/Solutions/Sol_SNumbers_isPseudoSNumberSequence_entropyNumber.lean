-- Prove2me | solution 1 for SNumbers.isPseudoSNumberSequence_entropyNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:50:20.352483+00:00
-- url     : https://prove2.me/submissions/0a400c47-615d-403e-b2fa-33198c62d338

module
public import Definitions.Def_SNumbers_Entropy
public import Definitions.Def_SNumbers_Inequalities
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_SVD
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Definitions.Def_SNumbers_EntropyBounds
public import Theorems.Thm_SNumbers_entropyNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_Additive_subadditive
public import Theorems.Thm_SNumbers_entropyNumber_add_le
public import Theorems.Thm_SNumbers_entropyNumber_antitone
public import Theorems.Thm_SNumbers_entropyNumber_comp_comp_le
public import Theorems.Thm_SNumbers_entropyNumber_nonneg


set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
namespace SNumbers
theorem _root_.solution :
    IsPseudoSNumberSequence (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => entropyNumber S n) where
  nonneg := fun S n => entropyNumber_nonneg S n
  norm_at_zero := fun S => entropyNumber_zero_eq_norm S
  antitone := fun S n => entropyNumber_antitone S n
  subadditive := fun S T n => entropyNumber_add_le S T n
  ideal := fun A S B n => entropyNumber_comp_comp_le B S A n
end SNumbers
