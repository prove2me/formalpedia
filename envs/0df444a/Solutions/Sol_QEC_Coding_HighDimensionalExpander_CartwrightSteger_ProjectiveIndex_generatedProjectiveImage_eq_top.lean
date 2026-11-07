-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.generatedProjectiveImage_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:43:03.60526+00:00
-- url     : https://prove2.me/submissions/5a984486-e182-4c4f-911e-9cae53efef0d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ProjectiveIndex_ker_sup_zpowers_eq_top_of_image_zpowers_eq_top
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ProjectiveIndex_ker_projectiveDetClass_eq_projectiveSpecialLinear


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
variable {G Q : Type*} [Group G] [Group Q]
variable (n K : Type*) [Fintype n] [DecidableEq n]
  [Nonempty n] [Field K] [Fintype K]
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
theorem _root_.solution
    (b : PGL(n, K))
    (horder : orderOf (projectiveDetClass n K b) =
      Nat.card (DetPowerClass n K)) :
    generatedProjectiveImage n K b = ⊤ := by
  have hz : Subgroup.zpowers (projectiveDetClass n K b) = ⊤ := by
    apply (Subgroup.card_eq_iff_eq_top
      (Subgroup.zpowers (projectiveDetClass n K b))).mp
    rw [Nat.card_zpowers, horder]
  rw [generatedProjectiveImage,
    ← ker_projectiveDetClass_eq_projectiveSpecialLinear n K]
  exact ker_sup_zpowers_eq_top_of_image_zpowers_eq_top
    (projectiveDetClass n K) b
    hz
end QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
