-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:46:24.85346+00:00
-- url     : https://prove2.me/submissions/9b2e82b9-ed95-40c3-9a0a-47b714d61d33

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFractionPullback_minpolyRoot
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCosetFractionRoot_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_finrank_bound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_integral
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
    (hN : 0<N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    Module.finrank (FractionRing (Polynomial ℂ)) (lpsOriginalGeneratedFunctionField N hN)=
      Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
  classical
  let := lpsOriginalJFractionEmbedding.toAlgebra
  apply le_antisymm (lpsOriginalGeneratedFunctionField_finrank_bound N hN)
  rw [show Module.finrank (FractionRing (Polynomial ℂ)) (lpsOriginalGeneratedFunctionField N hN)=
    (minpoly (FractionRing (Polynomial ℂ)) (lpsOriginalJNInFractionField N hN)).natDegree from
      IntermediateField.adjoin.finrank (lpsOriginalJNInFractionField_integral N hN)]
  let Q := minpoly (FractionRing (Polynomial ℂ)) (lpsOriginalJNInFractionField N hN)
  let P := Q.map (algebraMap (FractionRing (Polynomial ℂ)) LPSOriginalHolomorphicFractionField)
  let := Fintype.ofFinite (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  have hP : P≠0 := Polynomial.map_ne_zero
    (minpoly.ne_zero (lpsOriginalJNInFractionField_integral N hN))
  have hroot : ∀ x : 𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ,
      P.eval (lpsOriginalCosetFractionRoot N hN x)=0 := by
    intro x
    dsimp only [P]
    rw [Polynomial.eval_map]
    change Polynomial.aeval
      (lpsOriginalFractionPullback x.out (lpsOriginalJNInFractionField N hN)) Q=0
    exact lpsOriginalFractionPullback_minpolyRoot N hN x.out
  have hd : P.natDegree=Q.natDegree := Polynomial.natDegree_map _
  rw [Nat.card_eq_fintype_card]
  by_contra hc
  have hlt : P.natDegree<Fintype.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
    rw [hd];exact Nat.lt_of_not_ge hc
  exact hP (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (lpsOriginalCosetFractionRoot_injective N hN) hroot hlt)
end QEC.Coding.TannerLiftedProduct
