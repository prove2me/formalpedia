-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.quotientMk_eq_of_indexCartwrightStegerGenerator_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:49:35.671882+00:00
-- url     : https://prove2.me/submissions/4ace2f66-3967-4b9a-bc23-1cf73231550f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCartwrightStegerGeneratorGL_apply_self
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCartwrightStegerGeneratorGL_apply_first_second
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_eq_algebraMap_of_constantFrobenius_eq
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root


section
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
private theorem generalLinear_eq_of_projective_eq_of_diagonal_one
    {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (i : n) (A B : Matrix.GeneralLinearGroup n K)
    (hprojective : Matrix.ProjGenLinGroup.mk A =
      Matrix.ProjGenLinGroup.mk B)
    (hA : (A : Matrix n n K) i i = 1)
    (hB : (B : Matrix n n K) i i = 1) :
    A = B := by
  have hcenter : A⁻¹ * B ∈
      Subgroup.center (Matrix.GeneralLinearGroup n K) := by
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    rw [map_mul, map_inv, hprojective]
    simp
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
  obtain ⟨a, ha⟩ := hcenter
  have hB_eq : B = A * Matrix.GeneralLinearGroup.scalar n a := by
    calc
      B = A * (A⁻¹ * B) := by group
      _ = A * Matrix.GeneralLinearGroup.scalar n a := by rw [← ha]
  have hmatrix := congrArg Units.val hB_eq
  have hentry := congrFun (congrFun hmatrix i) i
  have haone : (1 : K) = a := by
    simpa [Matrix.GeneralLinearGroup.scalar, Matrix.mul_diagonal,
      Matrix.scalar_apply, hA, hB] using hentry
  have haunit : a = 1 := Units.ext haone.symm
  subst a
  simpa using hB_eq.symm
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (u v : (ConstantExtension P r)ˣ)
    (hprojective : indexCartwrightStegerGenerator P r level u =
      indexCartwrightStegerGenerator P r level v) :
    (QuotientGroup.mk u : ConstantProjectiveClass P r) =
      QuotientGroup.mk v := by
  have hgl :
      indexCartwrightStegerGeneratorGL P r level u =
        indexCartwrightStegerGeneratorGL P r level v :=
    generalLinear_eq_of_projective_eq_of_diagonal_one
      (generatorFirstIndex r)
      (indexCartwrightStegerGeneratorGL P r level u)
      (indexCartwrightStegerGeneratorGL P r level v)
      hprojective
      (indexCartwrightStegerGeneratorGL_apply_self P r level u _)
      (indexCartwrightStegerGeneratorGL_apply_self P r level v _)
  have hentry := congrArg
    (fun A : Matrix.GeneralLinearGroup (Fin r.matrixRank)
        (ResidueField P r level) =>
      (A : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level))
          (generatorFirstIndex r) (generatorSecondIndex r)) hgl
  change
    (indexCartwrightStegerGeneratorGL P r level u :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level))
        (generatorFirstIndex r) (generatorSecondIndex r) =
      (indexCartwrightStegerGeneratorGL P r level v :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level))
        (generatorFirstIndex r) (generatorSecondIndex r) at hentry
  rw [indexCartwrightStegerGeneratorGL_apply_first_second,
    indexCartwrightStegerGeneratorGL_apply_first_second] at hentry
  have hratio :
      (u : ConstantExtension P r) *
          ((constantFrobenius P r).symm
            (u : ConstantExtension P r))⁻¹ =
        (v : ConstantExtension P r) *
          ((constantFrobenius P r).symm
            (v : ConstantExtension P r))⁻¹ := by
    apply (indexConstantEmbedding P r level).injective
    exact neg_injective hentry
  have hsu :
    (constantFrobenius P r).symm
          (u : ConstantExtension P r) ≠ 0 :=
    fun hzero => Units.ne_zero u <|
      (constantFrobenius P r).symm.injective (by
        rw [map_zero]
        exact hzero)
  have hsv :
    (constantFrobenius P r).symm
          (v : ConstantExtension P r) ≠ 0 :=
    fun hzero => Units.ne_zero v <|
      (constantFrobenius P r).symm.injective (by
        rw [map_zero]
        exact hzero)
  have hdiv :
      (u : ConstantExtension P r) /
          (constantFrobenius P r).symm u =
        (v : ConstantExtension P r) /
          (constantFrobenius P r).symm v := by
    simpa [div_eq_mul_inv] using hratio
  have hcross :
      (u : ConstantExtension P r) *
          (constantFrobenius P r).symm v =
        (v : ConstantExtension P r) *
          (constantFrobenius P r).symm u :=
    (div_eq_div_iff hsu hsv).mp hdiv
  have hfixedSymm :
      (constantFrobenius P r).symm
          ((u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹) =
        (u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹ := by
    have hdiv2 :
        (constantFrobenius P r).symm (u : ConstantExtension P r) /
            (constantFrobenius P r).symm (v : ConstantExtension P r) =
          (u : ConstantExtension P r) / (v : ConstantExtension P r) := by
      apply (div_eq_div_iff hsv (Units.ne_zero v)).mpr
      simpa [mul_comm] using hcross.symm
    simpa [map_mul, map_inv, div_eq_mul_inv] using hdiv2
  have hfixed :
      constantFrobenius P r
          ((u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹) =
        (u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹ := by
    have h := congrArg (constantFrobenius P r) hfixedSymm
    simpa using h.symm
  obtain ⟨a, ha⟩ := exists_eq_algebraMap_of_constantFrobenius_eq
    P r ((u : ConstantExtension P r) * (v : ConstantExtension P r)⁻¹) hfixed
  have ha_ne : a ≠ 0 := by
    intro hzero
    have := ha
    rw [hzero, map_zero] at this
    exact (mul_ne_zero (Units.ne_zero u) (inv_ne_zero (Units.ne_zero v))) this.symm
  let au : (BaseField P)ˣ := Units.mk0 a ha_ne
  apply QuotientGroup.eq_iff_div_mem.mpr
  change u / v ∈ baseScalarUnits P r
  refine ⟨au, ?_⟩
  apply Units.ext
  simpa [au, baseScalarUnitHom, div_eq_mul_inv] using ha
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
