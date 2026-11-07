-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDilatedNorm_ne_zero_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:13:30.869491+00:00
-- url     : https://prove2.me/submissions/f4540d4b-56ab-4b31-8134-34ecd361c1d0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaDilatedForm_apply
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
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N)
    (τ : ℍ) : lpsOriginalDeltaDilatedNorm N hN τ≠0 := by
  classical
  let := Fintype.ofFinite (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  simp only [lpsOriginalDeltaDilatedNorm,ModularForm.coe_norm,Finset.prod_apply]
  apply Finset.prod_ne_zero_iff.mpr
  intro q hq
  induction q using Quotient.inductionOn with
  | h g =>
    have hd : (g.val⁻¹).det=1 := Subgroup.HasDetOne.det_eq (inv_mem g.property)
    have hf : lpsOriginalDeltaDilatedForm N hN (g.val⁻¹•τ)≠0 := by
      rw [lpsOriginalDeltaDilatedForm_apply]
      exact mul_ne_zero (pow_ne_zero 11 (by exact_mod_cast hN.ne'))
        (ModularForm.discriminant_ne_zero _)
    simp only [SlashInvariantForm.quotientFunc_mk,ModularForm.slash_apply,
      UpperHalfPlane.σ,hd,Units.val_one,zero_lt_one,ite_true,
      ContinuousAlgEquiv.refl_apply,abs_one,Complex.ofReal_one,one_zpow,mul_one]
    exact mul_ne_zero hf (zpow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ τ))
end QEC.Coding.TannerLiftedProduct
