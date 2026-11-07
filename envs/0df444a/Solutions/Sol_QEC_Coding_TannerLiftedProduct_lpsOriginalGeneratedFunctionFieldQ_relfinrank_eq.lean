-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionFieldQ_relfinrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:56:39.278377+00:00
-- url     : https://prove2.me/submissions/22f820ee-9f70-4251-97e9-ed0654b23ef8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_level_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_finiteDimensional
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_finrank_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (hposN : 0 < N) (hposM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hposN).relfinrank
      (lpsOriginalGeneratedFunctionFieldQ M hposM) =
      ((CongruenceSubgroup.Gamma0 M).subgroupOf
        (CongruenceSubgroup.Gamma0 N)).index := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalGeneratedFunctionFieldQ_finiteDimensional N hposN
  let GN : Subgroup (GL (Fin 2) ℝ) :=
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
  let GM : Subgroup (GL (Fin 2) ℝ) :=
    (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ))
  have hle : GM ≤ GN := Subgroup.map_mono (lpsGamma0_level_le N M hNM)
  have htop : GN ≤ 𝒮ℒ := (CongruenceSubgroup.Gamma0 N).map_le_range _
  have hG := Subgroup.relIndex_mul_relIndex GM GN 𝒮ℒ hle htop
  have hidx : GM.relIndex GN =
      ((CongruenceSubgroup.Gamma0 M).subgroupOf
        (CongruenceSubgroup.Gamma0 N)).index := by
    change ((CongruenceSubgroup.Gamma0 M).map (Matrix.SpecialLinearGroup.mapGL ℝ)).relIndex
      ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) = _
    exact Subgroup.relIndex_map_map_of_injective _ _ Matrix.SpecialLinearGroup.mapGL_injective
  rw [hidx] at hG
  have hF := IntermediateField.finrank_bot_mul_relfinrank
    (lpsOriginalGeneratedFunctionFieldQ_level_le N M hNM hN hposN hposM)
  rw [lpsOriginalGeneratedFunctionFieldQ_finrank_eq N hposN,
    lpsOriginalGeneratedFunctionFieldQ_finrank_eq M hposM] at hF
  change GN.relIndex 𝒮ℒ *
    (lpsOriginalGeneratedFunctionFieldQ N hposN).relfinrank
      (lpsOriginalGeneratedFunctionFieldQ M hposM) = GM.relIndex 𝒮ℒ at hF
  have hp : 0 < Module.finrank (FractionRing (Polynomial ℚ))
      (lpsOriginalGeneratedFunctionFieldQ N hposN) :=
    (Module.finrank_pos_iff_of_free (FractionRing (Polynomial ℚ))
      (lpsOriginalGeneratedFunctionFieldQ N hposN)).mpr inferInstance
  rw [lpsOriginalGeneratedFunctionFieldQ_finrank_eq N hposN] at hp
  change 0 < GN.relIndex 𝒮ℒ at hp
  apply Nat.eq_of_mul_eq_mul_left hp
  exact hF.trans (by simpa only [Nat.mul_comm] using hG.symm)
end QEC.Coding.TannerLiftedProduct
