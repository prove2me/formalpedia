-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_cusp_germ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:20:43.185682+00:00
-- url     : https://prove2.me/submissions/ddac3127-27a4-4dd0-8a66-c467715d1aac

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_cusp_param
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_target_open
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_target_zero
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
theorem _root_.solution (N : ℕ) [NeZero N]
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    (fun q : ℂ => lpsOriginalFilledJ N
      ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).symm q)) =ᶠ[𝓝[≠] 0]
    (fun q => lpsOriginalJQCoefficient
      (q^(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c))) /
      q^(lpsOriginalCuspWidthNat N (lpsOriginalCuspRepresentative N c))) := by
  let r := lpsOriginalCuspRepresentative N c
  let m := lpsOriginalCuspWidthNat N r
  let e := lpsOriginalFilledCuspPartialEquiv N r
  have htarget : ∀ᶠ q in 𝓝 (0:ℂ), q∈e.target :=
    (lpsOriginalFilledCuspPartialEquiv_target_open N r).mem_nhds
      (lpsOriginalFilledCuspPartialEquiv_target_zero N r)
  filter_upwards [nhdsWithin_le_nhds htarget,self_mem_nhdsWithin] with q hqt hq
  have hq0 : q≠0 := by simpa using hq
  have h := lpsOriginalFilledJ_cusp_param N c ⟨q,hqt⟩ hq0
  change q^m*lpsOriginalFilledJ N (e.symm q)=lpsOriginalJQCoefficient (q^m) at h
  exact (eq_div_iff (pow_ne_zero m hq0)).mpr (by rw [mul_comm];exact h)
end QEC.Coding.TannerLiftedProduct
