-- Prove2me | solution 1 for SNumbers.L2Linf.bernsteinNumber_crossS_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:39:04.41498+00:00
-- url     : https://prove2.me/submissions/c6cee9c8-85fc-4e76-8cb7-181fd5469ad2

module
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Operator.Prod
public import Definitions.Def_SNumbers_Examples_IdentityL2Linfty
public import Theorems.Thm_SNumbers_L2Linf_bernsteinNumber_idEmbed_two_infty_le
public import Theorems.Thm_SNumbers_bernsteinNumber_comp_comp_le
public import Theorems.Thm_SNumbers_bernsteinNumber_nonneg


set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal ComplexConjugate
open ContinuousLinearMap
open SNumbers SNumbers.L2Linf
variable {𝕜 : Type u} [RCLike 𝕜]
namespace SNumbers.L2Linf
theorem _root_.solution : bernsteinNumber (crossS (𝕜 := 𝕜)) 35 ≤ 1 / 6 := by
  have h : bernsteinNumber (crossS (𝕜 := 𝕜)) 35 ≤
      ‖inr 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ *
        bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 71) ∞ 2) 35 *
        ‖fst 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ :=
    bernsteinNumber_comp_comp_le _ _ _ 35
  have hB : bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 71) ∞ 2) 35 ≤ 1 / 6 := by
    have h6 : Real.sqrt (((35 : ℕ) : ℝ) + 1) = 6 := by
      rw [show ((35 : ℕ) : ℝ) + 1 = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have := bernsteinNumber_idEmbed_two_infty_le (𝕜 := 𝕜) 71 35
    rwa [h6] at this
  calc bernsteinNumber (crossS (𝕜 := 𝕜)) 35
      ≤ ‖inr 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ *
          bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 71) ∞ 2) 35 *
          ‖fst 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ := h
    _ ≤ 1 * (1 / 6) * 1 :=
        mul_le_mul (mul_le_mul (norm_inr_le_one 𝕜 _ _) hB (bernsteinNumber_nonneg _ _) zero_le_one)
          (ContinuousLinearMap.norm_fst_le 𝕜 _ _) (norm_nonneg _) (by norm_num)
    _ = 1 / 6 := by norm_num
end SNumbers.L2Linf
