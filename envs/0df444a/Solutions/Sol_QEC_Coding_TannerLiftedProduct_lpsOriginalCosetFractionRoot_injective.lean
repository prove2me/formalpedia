-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCosetFractionRoot_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:31:59.484912+00:00
-- url     : https://prove2.me/submissions/ef3e46ab-d4e3-4c9c-819f-18c7d11cd158

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilatedRealExactStabilizer
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0<N) :
    Function.Injective (lpsOriginalCosetFractionRoot N hN) := by
  intro x y he
  have hf : lpsOriginalHolomorphicPullback x.out (lpsOriginalJNHolomorphic N hN)=
      lpsOriginalHolomorphicPullback y.out (lpsOriginalJNHolomorphic N hN) := by
    apply IsFractionRing.injective LPSOriginalHolomorphicRing
      LPSOriginalHolomorphicFractionField
    simpa only [lpsOriginalCosetFractionRoot,lpsOriginalJNInFractionField,
      lpsOriginalFractionPullbackRing_localization] using he
  have hpoint : ∀ τ : ℍ,
      lpsOriginalJDilated N hN (x.out.val⁻¹•τ)=
        lpsOriginalJDilated N hN (y.out.val⁻¹•τ) := by
    intro τ
    exact congrArg (fun f : LPSOriginalHolomorphicRing=>f.val τ) hf
  have hg : (x.out⁻¹*y.out).val∈
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) := by
    apply (lpsOriginalJDilatedRealExactStabilizer N hN (x.out⁻¹*y.out)).mp
    intro τ
    simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_smul,inv_smul_smul] using
      hpoint (y.out.val•τ)
  have hrep : (QuotientGroup.mk x.out : 𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)=
        QuotientGroup.mk y.out := QuotientGroup.eq.mpr hg
  exact x.out_eq'.symm.trans (hrep.trans y.out_eq')
end QEC.Coding.TannerLiftedProduct
