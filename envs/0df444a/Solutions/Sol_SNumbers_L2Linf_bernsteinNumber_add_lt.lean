-- Prove2me | solution 1 for SNumbers.L2Linf.bernsteinNumber_add_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:50:10.953796+00:00
-- url     : https://prove2.me/submissions/836e50bf-8f44-47b2-81d8-d831abd5cba1

module
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Operator.Prod
public import Definitions.Def_SNumbers_Examples_IdentityL2Linfty
public import Theorems.Thm_SNumbers_L2Linf_inv_three_le_bernsteinNumber_crossS_add_crossT
public import Theorems.Thm_SNumbers_L2Linf_bernsteinNumber_crossS_le
public import Theorems.Thm_SNumbers_L2Linf_bernsteinNumber_crossT_le

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal ComplexConjugate
open ContinuousLinearMap
open SNumbers SNumbers.L2Linf
variable {𝕜 : Type u} [RCLike 𝕜]
namespace SNumbers.L2Linf
theorem _root_.solution :
    bernsteinNumber (crossS (𝕜 := 𝕜)) 35 + bernsteinNumber (crossT (𝕜 := 𝕜)) 35 <
      bernsteinNumber (crossS (𝕜 := 𝕜) + crossT) (35 + 35) := by
  have hS := bernsteinNumber_crossS_le (𝕜 := 𝕜)
  have hT := bernsteinNumber_crossT_le (𝕜 := 𝕜)
  have h := inv_three_le_bernsteinNumber_crossS_add_crossT (𝕜 := 𝕜)
  -- `√(71/36) < 3/2`, since `71/36 < 81/36`
  have hsqrt : Real.sqrt (71 / 36) < 3 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith
end SNumbers.L2Linf
