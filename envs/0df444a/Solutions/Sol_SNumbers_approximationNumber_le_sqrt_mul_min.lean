-- Prove2me | solution 1 for SNumbers.approximationNumber_le_sqrt_mul_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:47:15.090149+00:00
-- url     : https://prove2.me/submissions/13b2da7a-fed6-4dd8-b72d-4784b7b6a708

module
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_SingularValuesFinDim
public import Definitions.Def_BasicResults_GarlingGordon
public import Definitions.Def_BasicResults_KadetsSnobar
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_SNumbers_Inequalities
public import Theorems.Thm_SNumbers_approximationNumber_le_sqrt_mul_gelfandNumber
public import Theorems.Thm_SNumbers_approximationNumber_le_sqrt_mul_kolmogorovNumber

set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X] [CompleteSpace Y]
omit [CompleteSpace X] [CompleteSpace Y]
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤
      (1 + Real.sqrt n) * min (gelfandNumber S n) (kolmogorovNumber S n) := by
  rcases le_total (gelfandNumber S n) (kolmogorovNumber S n) with h | h
  · rw [min_eq_left h]
    exact approximationNumber_le_sqrt_mul_gelfandNumber S n
  · rw [min_eq_right h]
    exact approximationNumber_le_sqrt_mul_kolmogorovNumber S n
end SNumbers
