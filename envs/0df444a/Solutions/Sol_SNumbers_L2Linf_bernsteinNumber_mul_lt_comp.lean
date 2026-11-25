-- Prove2me | solution 1 for SNumbers.L2Linf.bernsteinNumber_mul_lt_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:36:40.80762+00:00
-- url     : https://prove2.me/submissions/86999a81-2e6b-4583-8ea0-3d009fe8f2e0

module
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Operator.Prod
public import Definitions.Def_SNumbers_Examples_IdentityL2Linfty
public import Theorems.Thm_SNumbers_L2Linf_bernsteinNumber_idEmbed_two_infty_le
public import Theorems.Thm_SNumbers_L2Linf_bernsteinNumber_idEmbed_infty_two_le
public import Theorems.Thm_SNumbers_L2Linf_idEmbed_two_infty_comp_idEmbed_infty_two
public import Theorems.Thm_SNumbers_bernsteinNumber_nonneg
public import Theorems.Thm_SNumbers_bernsteinNumber_strict
public import Theorems.Thm_SNumbers_finrank_piLp


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
    bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 3) 2 ∞) 1 *
        bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 3) ∞ 2) 1 <
      bernsteinNumber ((idEmbed (𝕜 := 𝕜) (m := 3) 2 ∞).comp (idEmbed ∞ 2)) (1 + 1) := by
  rw [idEmbed_two_infty_comp_idEmbed_infty_two,
    bernsteinNumber_strict _ (Module.lt_rank_of_lt_finrank (by rw [finrank_piLp]; norm_num))]
  have hS : bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 3) 2 ∞) 1 ≤ Real.sqrt (3 / 2) := by
    convert bernsteinNumber_idEmbed_infty_two_le (𝕜 := 𝕜) 3 1 using 2; norm_num
  have hT : bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 3) ∞ 2) 1 ≤ 1 / Real.sqrt 2 := by
    convert bernsteinNumber_idEmbed_two_infty_le (𝕜 := 𝕜) 3 1 using 3; norm_num
  -- `√(3/2) · (1/√2) < 1`, since `3/2 < 2`
  have hlt : Real.sqrt (3 / 2) * (1 / Real.sqrt 2) < 1 := by
    rw [mul_one_div, div_lt_one (Real.sqrt_pos.mpr (by norm_num))]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  calc bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 3) 2 ∞) 1 *
        bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 3) ∞ 2) 1
      ≤ Real.sqrt (3 / 2) * (1 / Real.sqrt 2) :=
        mul_le_mul hS hT (bernsteinNumber_nonneg _ _) (Real.sqrt_nonneg _)
    _ < 1 := hlt
end SNumbers.L2Linf
