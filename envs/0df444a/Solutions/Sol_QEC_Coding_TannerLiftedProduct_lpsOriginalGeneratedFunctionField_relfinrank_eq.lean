-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_relfinrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:46:26.757966+00:00
-- url     : https://prove2.me/submissions/99c0ca68-a85c-4b8d-87b2-1903593b8e60

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelFibres
import Mathlib.FieldTheory.Relrank
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_finiteDimensional
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_finrank_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_level_le
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
open scoped MatrixGroups UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (hposN : 0 < N) (hposM : 0 < M) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    (lpsOriginalGeneratedFunctionField N hposN).relfinrank
      (lpsOriginalGeneratedFunctionField M hposM) =
      ((CongruenceSubgroup.Gamma0 M).subgroupOf
        (CongruenceSubgroup.Gamma0 N)).index := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let := lpsOriginalGeneratedFunctionField_finiteDimensional N hposN
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
    (lpsOriginalGeneratedFunctionField_level_le N M hNM hN hposN hposM)
  rw [lpsOriginalGeneratedFunctionField_finrank_eq N hposN,
    lpsOriginalGeneratedFunctionField_finrank_eq M hposM] at hF
  change GN.relIndex 𝒮ℒ *
    (lpsOriginalGeneratedFunctionField N hposN).relfinrank
      (lpsOriginalGeneratedFunctionField M hposM) = GM.relIndex 𝒮ℒ at hF
  have hp : 0 < Module.finrank (FractionRing (Polynomial ℂ))
      (lpsOriginalGeneratedFunctionField N hposN) :=
    (Module.finrank_pos_iff_of_free (FractionRing (Polynomial ℂ))
      (lpsOriginalGeneratedFunctionField N hposN)).mpr inferInstance
  rw [lpsOriginalGeneratedFunctionField_finrank_eq N hposN] at hp
  change 0 < GN.relIndex 𝒮ℒ at hp
  apply Nat.eq_of_mul_eq_mul_left hp
  exact hF.trans (by simpa only [Nat.mul_comm] using hG.symm)
end QEC.Coding.TannerLiftedProduct
