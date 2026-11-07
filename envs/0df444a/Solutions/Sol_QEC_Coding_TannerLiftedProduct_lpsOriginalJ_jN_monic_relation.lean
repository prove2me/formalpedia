-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJ_jN_monic_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:33:54.918446+00:00
-- url     : https://prove2.me/submissions/82671bcf-0618-4664-9426-d411be0bfced

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaDilatedNorm_delta_scalar
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularEquationComplex_degree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularEquationComplex_top_coeff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularEquationComplex_original_root
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
    ∃ Φ : Polynomial (Polynomial ℂ), Φ.Monic ∧
      Φ.natDegree=Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∧ ∀ τ : ℍ,
      Φ.eval₂ (Polynomial.evalRingHom (lpsOriginalJInvariant τ))
        (lpsOriginalJDilated N hN τ)=0 := by
  obtain ⟨lam,hlam0,hlam⟩ := lpsOriginalDeltaDilatedNorm_delta_scalar N hN
  let r := Nat.card (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  let μ := (-1:ℂ)^r*lam
  have hμ : μ≠0 := mul_ne_zero (pow_ne_zero r (by norm_num)) hlam0
  let Φ : Polynomial (Polynomial ℂ) :=
    Polynomial.C (Polynomial.C μ⁻¹)*lpsOriginalModularEquationComplex N hN
  have hdeg : Φ.natDegree≤r :=
    Polynomial.natDegree_mul_le.trans (by
      simpa only [Polynomial.natDegree_C,zero_add] using
        lpsOriginalModularEquationComplex_degree N hN)
  have hcoeff : Φ.coeff r=1 := by
    rw [Polynomial.coeff_C_mul,lpsOriginalModularEquationComplex_top_coeff N hN lam hlam,
      ←Polynomial.C_mul,inv_mul_cancel₀ hμ,Polynomial.C_1]
  have heq : Φ.natDegree=r :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg (by rw [hcoeff];exact one_ne_zero)
  refine ⟨Φ,?_,heq,?_⟩
  · change Φ.coeff Φ.natDegree=1
    rw [heq,hcoeff]
  · intro τ
    simp only [Φ,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.coe_evalRingHom,
      Polynomial.eval_C,lpsOriginalModularEquationComplex_original_root,mul_zero]
end QEC.Coding.TannerLiftedProduct
