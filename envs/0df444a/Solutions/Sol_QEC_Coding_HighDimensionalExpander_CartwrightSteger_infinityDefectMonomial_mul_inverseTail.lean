-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityDefectMonomial_mul_inverseTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:28:53.070957+00:00
-- url     : https://prove2.me/submissions/b8154a26-8d36-41df-ac94-929f7dcbdeaf

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrixHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorMatrix_pow_mul_constantMatrix
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorInverseMatrix_mul_constantMatrix
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_rank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityConjugationCorrectionSum_bound_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCompactCyclicSemidirectHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingGeneratorNeighborAtEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueBGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionSpecial_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCompactCyclicSemidirectHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingGeneratorNeighborAtEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerNormUnit_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueBGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_three
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeFundamentalHeckeAlgEquiv_apply


attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrixHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_rank
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCorrectionSum_bound_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k : ℕ) (ζ : ConstantExtension P r) :
    infinityDefectMonomial P r u k ζ *
        constantConjugatedBInverseTail P r u =
      ∑ i ∈ Finset.range r.matrixRank,
        constantMatrix P r
            ((infinityCyclicInverseCoefficient P r u *
                (constantFrobenius P r).symm ζ) *
              (constantFrobenius P r).symm
                ((constantFrobenius P r ^ k)
                  (infinityCyclicCoefficient P r u i :
                    ConstantExtension P r))) *
          cyclicGeneratorInverseMatrix P r *
            cyclicGeneratorMatrix P r ^ (k + i) := by
  rw [infinityDefectMonomial, constantConjugatedBInverseTail]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc
    (constantMatrix P r
        (infinityCyclicInverseCoefficient P r u *
          (constantFrobenius P r).symm ζ) *
      cyclicGeneratorInverseMatrix P r)
    (cyclicGeneratorMatrix P r ^ k)
    (constantMatrix P r
        (infinityCyclicCoefficient P r u i : ConstantExtension P r) *
      cyclicGeneratorMatrix P r ^ i)]
  rw [← mul_assoc (cyclicGeneratorMatrix P r ^ k)
    (constantMatrix P r
      (infinityCyclicCoefficient P r u i : ConstantExtension P r))
    (cyclicGeneratorMatrix P r ^ i)]
  rw [cyclicGeneratorMatrix_pow_mul_constantMatrix]
  rw [mul_assoc
    (constantMatrix P r
      ((constantFrobenius P r ^ k)
        (infinityCyclicCoefficient P r u i : ConstantExtension P r)))
    (cyclicGeneratorMatrix P r ^ k)
    (cyclicGeneratorMatrix P r ^ i)]
  rw [mul_assoc
    (constantMatrix P r
      (infinityCyclicInverseCoefficient P r u *
        (constantFrobenius P r).symm ζ))
    (cyclicGeneratorInverseMatrix P r)]
  rw [← mul_assoc (cyclicGeneratorInverseMatrix P r),
    cyclicGeneratorInverseMatrix_mul_constantMatrix]
  rw [mul_assoc
    (constantMatrix P r
      ((constantFrobenius P r).symm
        ((constantFrobenius P r ^ k)
          (infinityCyclicCoefficient P r u i : ConstantExtension P r))))
    (cyclicGeneratorInverseMatrix P r)]
  rw [← mul_assoc
    (constantMatrix P r
      (infinityCyclicInverseCoefficient P r u *
        (constantFrobenius P r).symm ζ))
    (constantMatrix P r
      ((constantFrobenius P r).symm
        ((constantFrobenius P r ^ k)
          (infinityCyclicCoefficient P r u i : ConstantExtension P r))))
    (cyclicGeneratorInverseMatrix P r *
      (cyclicGeneratorMatrix P r ^ k * cyclicGeneratorMatrix P r ^ i))]
  change
    (constantMatrixEmbedding P r
          (infinityCyclicInverseCoefficient P r u *
            (constantFrobenius P r).symm ζ) *
        constantMatrixEmbedding P r
          ((constantFrobenius P r).symm
            ((constantFrobenius P r ^ k)
              (infinityCyclicCoefficient P r u i : ConstantExtension P r)))) *
        (cyclicGeneratorInverseMatrix P r *
          (cyclicGeneratorMatrix P r ^ k * cyclicGeneratorMatrix P r ^ i)) = _
  rw [← map_mul, ← pow_add]
  simp only [constantMatrixEmbedding_apply]
  rw [← mul_assoc]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
