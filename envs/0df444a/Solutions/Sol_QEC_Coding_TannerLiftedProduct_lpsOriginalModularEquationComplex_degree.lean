-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalModularEquationComplex_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:20:03.468082+00:00
-- url     : https://prove2.me/submissions/4704f59a-23c0-4691-8b01-8b4cdc749821

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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJPolynomialEvalHom_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJPolynomialEvalHom_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularCosetPolynomial_degree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularEquationComplex_recovery
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
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N) :
    (lpsOriginalModularEquationComplex N hN).natDegree≤Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  apply lpsOriginalJPolynomialEvalHom_injective
  funext τ
  simp only [lpsOriginalJPolynomialEvalHom_apply,Polynomial.eval_zero]
  have h := congrArg (fun P : Polynomial ℂ => P.coeff k)
    (lpsOriginalModularEquationComplex_recovery N hN τ)
  rw [Polynomial.coeff_C_mul,Polynomial.coeff_map,
    Polynomial.natDegree_le_iff_coeff_eq_zero.mp (lpsOriginalModularCosetPolynomial_degree N hN τ) k hk] at h
  exact (mul_eq_zero.mp h).resolve_left
    (pow_ne_zero _ (ModularForm.discriminant_ne_zero τ))
end QEC.Coding.TannerLiftedProduct
