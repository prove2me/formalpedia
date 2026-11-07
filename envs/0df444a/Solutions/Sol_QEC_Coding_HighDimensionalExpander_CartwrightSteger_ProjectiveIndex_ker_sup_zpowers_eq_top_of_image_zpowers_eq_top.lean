-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.ker_sup_zpowers_eq_top_of_image_zpowers_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:41:57.83065+00:00
-- url     : https://prove2.me/submissions/9649c8b4-14ac-4421-9c16-818c412da2e5

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
variable {G Q : Type*} [Group G] [Group Q]
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
theorem _root_.solution
    (f : G →* Q) (b : G)
    (hb : Subgroup.zpowers (f b) = ⊤) :
    f.ker ⊔ Subgroup.zpowers b = ⊤ := by
  apply top_unique
  intro g _
  have hfg : f g ∈ Subgroup.zpowers (f b) := by
    rw [hb]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hfg
  have hker : g * b ^ (-k) ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_zpow, ← hk]
    simp
  have hzpow : b ^ k ∈ Subgroup.zpowers b :=
    Subgroup.zpow_mem_zpowers b k
  have hproduct : (g * b ^ (-k)) * b ^ k ∈
      f.ker ⊔ Subgroup.zpowers b :=
    Subgroup.mul_mem_sup hker hzpow
  simpa [← mul_assoc] using hproduct
end QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
