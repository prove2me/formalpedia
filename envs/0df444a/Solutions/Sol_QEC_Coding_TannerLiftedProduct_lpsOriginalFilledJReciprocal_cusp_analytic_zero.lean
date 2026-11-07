-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_cusp_analytic_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:14:44.724566+00:00
-- url     : https://prove2.me/submissions/875520d4-3303-4700-81ce-487b00a58352

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJReciprocal_cusp_formula
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspWidthNat_positive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspParam_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_target_open
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspPartialEquiv_target_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQCoefficient_analytic_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQCoefficient_zero
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
theorem _root_.solution (N : ℕ) [NeZero N] (a : ℂ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    AnalyticAt ℂ (fun q : ℂ => lpsOriginalFilledJReciprocal N a
      ((lpsOriginalFilledCuspPartialEquiv N (lpsOriginalCuspRepresentative N c)).symm q)) 0 := by
  let r := lpsOriginalCuspRepresentative N c
  let m := lpsOriginalCuspWidthNat N r
  let e := lpsOriginalFilledCuspPartialEquiv N r
  have hm : 0<m := lpsOriginalCuspWidthNat_positive N r
  have ha : AnalyticAt ℂ (fun q : ℂ => lpsOriginalJQCoefficient (q^m)) 0 := by
    apply lpsOriginalJQCoefficient_analytic_zero.comp_of_eq (analyticAt_id.pow m)
    simp [Nat.ne_of_gt hm]
  have hd : AnalyticAt ℂ (fun q : ℂ => lpsOriginalJQCoefficient (q^m)-a*q^m) 0 :=
    ha.sub (analyticAt_const.mul (analyticAt_id.pow m))
  have hn : lpsOriginalJQCoefficient ((0:ℂ)^m)-a*(0:ℂ)^m≠0 := by
    simp [Nat.ne_of_gt hm,lpsOriginalJQCoefficient_zero]
  have hf := (analyticAt_id.pow m).mul (hd.inv hn)
  apply hf.congr
  have htarget : ∀ᶠ q in 𝓝 (0:ℂ), q∈e.target :=
    (lpsOriginalFilledCuspPartialEquiv_target_open N r).mem_nhds
      (lpsOriginalFilledCuspPartialEquiv_target_zero N r)
  filter_upwards [htarget] with q hq
  by_cases hq0 : q=0
  · subst q
    have hz := lpsOriginalFilledCuspParam_zero N c ⟨0,hq⟩ rfl
    change e.symm 0=Sum.inr c at hz
    rw [hz]
    simp [lpsOriginalFilledJReciprocal,Nat.ne_of_gt hm]
  · have he := lpsOriginalFilledJReciprocal_cusp_formula N a c ⟨q,hq⟩ hq0
    change q^m*(lpsOriginalJQCoefficient (q^m)-a*q^m)⁻¹=
      lpsOriginalFilledJReciprocal N a (e.symm q)
    simpa only [div_eq_mul_inv,m,r,e,lpsOriginalFilledCuspParam,
      lpsOriginalFilledCuspPartialEquiv,PartialEquiv.coe_symm_mk] using he.symm
end QEC.Coding.TannerLiftedProduct
