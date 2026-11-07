-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex.ker_projectiveDetClass_eq_projectiveSpecialLinear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:38:44.80607+00:00
-- url     : https://prove2.me/submissions/5dbab440-0427-443a-bbb0-4dc63db5fa1a

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_ProjectiveIndex_projectiveDetClass_mk
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
variable (n K : Type*) [Fintype n] [DecidableEq n]
  [Nonempty n] [Field K] [Fintype K]
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
theorem _root_.solution :
    (projectiveDetClass n K).ker = projectiveSpecialLinear n K := by
  ext g
  constructor
  · intro hg
    refine Matrix.ProjGenLinGroup.induction_on g ?_ hg
    intro A hA
    change
      ((Matrix.GeneralLinearGroup.det A : Kˣ) : DetPowerClass n K) = 1 at hA
    have hmem : Matrix.GeneralLinearGroup.det A ∈
        (powMonoidHom (Fintype.card n) : Kˣ →* Kˣ).range :=
      (QuotientGroup.eq_one_iff _).1 hA
    obtain ⟨u, hu⟩ := hmem
    let B : Matrix.GeneralLinearGroup n K :=
      Matrix.GeneralLinearGroup.scalar n u⁻¹ * A
    have hdetB : Matrix.det (B : Matrix n n K) = 1 := by
      have huval := congrArg Units.val hu
      dsimp [B]
      rw [Matrix.det_mul, Matrix.det_diagonal]
      simp only [Finset.prod_const, Finset.card_univ]
      simp only [Units.val_inv_eq_inv_val]
      change (u : K) ^ Fintype.card n =
        Matrix.det (A : Matrix n n K) at huval
      change (u : K)⁻¹ ^ Fintype.card n *
        Matrix.det (A : Matrix n n K) = 1
      rw [← huval]
      simp
    let s : Matrix.SpecialLinearGroup n K := ⟨(B : Matrix n n K), hdetB⟩
    refine ⟨s, ?_⟩
    change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL s) =
      Matrix.ProjGenLinGroup.mk A
    have hsB : Matrix.SpecialLinearGroup.toGL s = B := by
      apply Units.ext
      rfl
    rw [hsB]
    dsimp [B]
    rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]
  · rintro ⟨s, rfl⟩
    rw [MonoidHom.mem_ker]
    change projectiveDetClass n K
      (Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL s)) = 1
    rw [projectiveDetClass_mk]
    apply (QuotientGroup.eq_one_iff _).2
    refine ⟨1, ?_⟩
    ext
    simp
end QEC.Coding.HighDimensionalExpander.CartwrightSteger.ProjectiveIndex
