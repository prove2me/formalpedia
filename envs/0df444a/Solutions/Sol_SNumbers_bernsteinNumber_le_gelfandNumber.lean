-- Prove2me | solution 1 for SNumbers.bernsteinNumber_le_gelfandNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:46:44.874311+00:00
-- url     : https://prove2.me/submissions/bc53f3d2-48b0-4a88-9b67-4e9330fa6550

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
public import Theorems.Thm_SNumbers_bernsteinNumber_le_of_injective_strict
public import Theorems.Thm_SNumbers_injective_gelfandNumber
public import Theorems.Thm_SNumbers_isStrictSNumberSequence_gelfandNumber


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
namespace SNumbers
theorem _root_.solution (S : X →L[𝕜] Y) (n : ℕ) :
    bernsteinNumber S n ≤ gelfandNumber S n :=
  bernsteinNumber_le_of_injective_strict
    isStrictSNumberSequence_gelfandNumber injective_gelfandNumber S n
end SNumbers
