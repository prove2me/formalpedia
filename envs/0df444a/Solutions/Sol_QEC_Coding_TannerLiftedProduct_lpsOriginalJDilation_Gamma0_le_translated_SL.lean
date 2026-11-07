-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJDilation_Gamma0_le_translated_SL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:27:43.625273+00:00
-- url     : https://prove2.me/submissions/d11ed674-b86c-4fe3-bc39-bc55086e6309

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilation_commute
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0<N) :
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (lpsE2AffineMatrix N hN 0)⁻¹ •
        (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) := by
  intro g hg
  obtain ⟨γ,hγ,rfl⟩ := hg
  change γ∈CongruenceSubgroup.Gamma0 N at hγ
  rw [CongruenceSubgroup.Gamma0_mem] at hγ
  have hdvd : (N:ℤ)∣γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) N).mp hγ
  obtain ⟨k,hk⟩ := hdvd
  rw [ConjAct.toConjAct_inv,Subgroup.mem_inv_pointwise_smul_iff,ConjAct.toConjAct_smul]
  refine ⟨lpsE2DilationConjugate N γ k hk,?_⟩
  have h := lpsOriginalJDilation_commute N hN γ k hk
  calc
    Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2DilationConjugate N γ k hk) =
      (Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2DilationConjugate N γ k hk) *
        lpsE2AffineMatrix N hN 0) * (lpsE2AffineMatrix N hN 0)⁻¹ := by simp
    _ = _ := by rw [h]
end QEC.Coding.TannerLiftedProduct
