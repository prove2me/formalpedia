-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalModularEquationComplex_recovery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:16:39.472193+00:00
-- url     : https://prove2.me/submissions/7abac1e1-be7a-4933-9056-c7c5f84707b4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularCosetPolynomial_eval
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularCosetPolynomial_degree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularNormCoefficient_spec
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularInterpolationNodes_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularEquationComplex_map
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
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 0<N)
    (τ : ℍ) :
    Polynomial.C (ModularForm.discriminant τ^(Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)))*
      (lpsOriginalModularEquationComplex N hN).map
        (Polynomial.evalRingHom (lpsOriginalJInvariant τ))=
      lpsOriginalModularCosetPolynomial N hN τ := by
  classical
  let r := Nat.card (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  let d := ModularForm.discriminant τ^r
  rw [lpsOriginalModularEquationComplex_map]
  have hm : Polynomial.C d*Lagrange.interpolate (Finset.univ:Finset (Fin (r+1)))
      (fun i => (i.val:ℂ))
      (fun i => (lpsOriginalModularNormCoefficient N hN (i.val:ℂ)).eval
        (lpsOriginalJInvariant τ))=
      Lagrange.interpolate (Finset.univ:Finset (Fin (r+1))) (fun i => (i.val:ℂ))
        (fun i => d*(lpsOriginalModularNormCoefficient N hN (i.val:ℂ)).eval
          (lpsOriginalJInvariant τ)) := by
    simp only [Lagrange.interpolate_apply,Finset.mul_sum,Polynomial.C_mul,mul_assoc]
  rw [hm]
  symm
  apply Lagrange.eq_interpolate_of_eval_eq _
    (lpsOriginalModularInterpolationNodes_injective r).injOn
  · apply Polynomial.degree_le_natDegree.trans_lt
    have hh := Nat.lt_succ_of_le (lpsOriginalModularCosetPolynomial_degree N hN τ)
    simp only [Finset.card_univ,Fintype.card_fin]
    exact_mod_cast hh
  · intro i hi
    rw [lpsOriginalModularCosetPolynomial_eval]
    exact (lpsOriginalModularNormCoefficient_spec N hN (i.val:ℂ)).2 τ
end QEC.Coding.TannerLiftedProduct
