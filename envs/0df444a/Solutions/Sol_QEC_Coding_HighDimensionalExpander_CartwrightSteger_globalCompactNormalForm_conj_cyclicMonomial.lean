-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalCompactNormalForm_conj_cyclicMonomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:35:38.578069+00:00
-- url     : https://prove2.me/submissions/a056bca1-7e65-4937-b987-8168aa345ad9

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGenerator_pow_conj_constantMatrix
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCompactCyclicSemidirectHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingGeneratorNeighborAtEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerNormUnit_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrixHom_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorMatrix_pow_mul_constantMatrix
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_frobeniusPowerEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCyclicGeneratorGL_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityConjugationCorrectionSum_bound_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_rank
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCyclicCoefficient_zero
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
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrixHom_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.frobeniusPowerEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCyclicGeneratorGL_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCorrectionSum_bound_zero
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_rank
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCyclicCoefficient_zero
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



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (j : ℕ) (c : ConstantExtension P r) (k : ℕ) :
    infinityConjugationLinearMap P r
        (globalCompactNormalForm P r u j)
        (constantMatrix P r c * cyclicGeneratorMatrix P r ^ k) =
      constantMatrix P r (compactConjugationDiagonalBlock P r u j k c) *
        cyclicGeneratorMatrix P r ^ k := by
  let Zj : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) := cyclicGeneratorMatrix P r ^ j
  let Zk : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) := cyclicGeneratorMatrix P r ^ k
  let ZjInv : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
    (((cyclicGenerator P r ^ j)⁻¹ :
        Matrix.GeneralLinearGroup (Fin r.matrixRank)
          (SplittingFunctionField P r)) :
      Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (SplittingFunctionField P r))
  let U : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) := constantMatrix P r u
  let UInv : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r) :=
    constantMatrix P r (u⁻¹ : (ConstantExtension P r)ˣ)
  have hcomm : Zk * ZjInv = ZjInv * Zk := by
    have hgroup : cyclicGenerator P r ^ k * (cyclicGenerator P r ^ j)⁻¹ =
        (cyclicGenerator P r ^ j)⁻¹ * cyclicGenerator P r ^ k := by group
    exact congrArg Units.val hgroup
  have hZjConj : Zj * constantMatrix P r c * ZjInv =
      constantMatrix P r ((constantFrobenius P r ^ j) c) := by
    exact cyclicGenerator_pow_conj_constantMatrix P r j c
  have hZkUInv : Zk * UInv =
      constantMatrix P r
          ((constantFrobenius P r ^ k) (u⁻¹ : ConstantExtension P r)) * Zk := by
    simpa [Zk, UInv] using
      cyclicGeneratorMatrix_pow_mul_constantMatrix P r k
        (u⁻¹ : ConstantExtension P r)
  change (U * Zj) * (constantMatrix P r c * Zk) * (ZjInv * UInv) = _
  calc
    (U * Zj) * (constantMatrix P r c * Zk) * (ZjInv * UInv) =
        U * (Zj * constantMatrix P r c * ZjInv) * Zk * UInv := by
          simp only [mul_assoc]
          rw [← mul_assoc Zk ZjInv UInv, hcomm]
          simp only [mul_assoc]
    _ = U * constantMatrix P r ((constantFrobenius P r ^ j) c) *
          Zk * UInv := by rw [hZjConj]
    _ = U * constantMatrix P r ((constantFrobenius P r ^ j) c) *
          (constantMatrix P r
            ((constantFrobenius P r ^ k) (u⁻¹ : ConstantExtension P r)) * Zk) := by
          rw [← hZkUInv, mul_assoc]
    _ = constantMatrix P r
          ((u : ConstantExtension P r) *
            (constantFrobenius P r ^ j) c *
            (constantFrobenius P r ^ k) (u⁻¹ : ConstantExtension P r)) * Zk := by
      dsimp [U]
      rw [← mul_assoc]
      rw [← constantMatrixEmbedding_apply, ← constantMatrixEmbedding_apply,
        ← constantMatrixEmbedding_apply, ← map_mul, ← map_mul]
      rw [constantMatrixEmbedding_apply]
    _ = constantMatrix P r (compactConjugationDiagonalBlock P r u j k c) *
          Zk := by
      simp only [compactConjugationDiagonalBlock,
        compactConjugationDiagonalMultiplier, LinearMap.comp_apply]
      change constantMatrix P r ((u : ConstantExtension P r) *
          (constantFrobenius P r ^ j) c *
          (constantFrobenius P r ^ k) (u⁻¹ : ConstantExtension P r)) * Zk =
        constantMatrix P r (((u : ConstantExtension P r) *
          ((constantFrobenius P r ^ k) (u : ConstantExtension P r))⁻¹) *
            (constantFrobenius P r ^ j) c) * Zk
      congr 2
      rw [map_inv₀]
      ring
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
