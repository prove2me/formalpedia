-- Prove2me | solution 1 for SNumbers.L2Linf.bernsteinNumber_crossT_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:39:37.962863+00:00
-- url     : https://prove2.me/submissions/93f9dd2c-7bd9-416c-98cd-706aa8f89d08

module
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Operator.Prod
public import Definitions.Def_SNumbers_Examples_IdentityL2Linfty
public import Theorems.Thm_SNumbers_L2Linf_bernsteinNumber_idEmbed_infty_two_le
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
theorem _root_.solution :
    bernsteinNumber (crossT (𝕜 := 𝕜)) 35 ≤ Real.sqrt (71 / 36) / 9 := by
  have h : bernsteinNumber (crossT (𝕜 := 𝕜)) 35 ≤
      ‖inl 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ *
        bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 71) 2 ∞) 35 *
        ‖(9 : 𝕜)⁻¹ • snd 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ :=
    bernsteinNumber_comp_comp_le _ _ _ 35
  have hB : bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 71) 2 ∞) 35 ≤ Real.sqrt (71 / 36) := by
    convert bernsteinNumber_idEmbed_infty_two_le (𝕜 := 𝕜) 71 35 using 2; norm_num
  have hsnd : ‖(9 : 𝕜)⁻¹ •
      snd 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ ≤ 9⁻¹ := by
    calc _ ≤ ‖(9 : 𝕜)⁻¹‖ *
          ‖snd 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ :=
          norm_smul_le _ _
      _ ≤ 9⁻¹ * 1 := by
          rw [norm_inv, RCLike.norm_ofNat]
          exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le 𝕜 _ _) (by norm_num)
      _ = 9⁻¹ := mul_one _
  calc bernsteinNumber (crossT (𝕜 := 𝕜)) 35
      ≤ ‖inl 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ *
          bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 71) 2 ∞) 35 *
          ‖(9 : 𝕜)⁻¹ • snd 𝕜 (PiLp 2 (fun _ : Fin 71 => 𝕜)) (PiLp ∞ (fun _ : Fin 71 => 𝕜))‖ :=
        h
    _ ≤ 1 * Real.sqrt (71 / 36) * 9⁻¹ :=
        mul_le_mul (mul_le_mul (norm_inl_le_one 𝕜 _ _) hB (bernsteinNumber_nonneg _ _) zero_le_one)
          hsnd (norm_nonneg _) (by positivity)
    _ = Real.sqrt (71 / 36) / 9 := by ring
end SNumbers.L2Linf
