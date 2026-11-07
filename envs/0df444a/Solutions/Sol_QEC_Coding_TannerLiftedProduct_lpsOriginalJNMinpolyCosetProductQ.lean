-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJNMinpolyCosetProductQ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:52:40.722202+00:00
-- url     : https://prove2.me/submissions/f2d48691-8b3d-4d6e-9dc4-537e551c5455

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNMinpolyDegreeQ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCosetFractionRoot_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFractionPullback_minpolyRootQ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_integralQ
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
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := Fintype.ofFinite (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
    (minpoly (FractionRing (Polynomial ℚ)) (lpsOriginalJNInFractionField N hN)).map
        lpsOriginalJFractionEmbeddingQ =
      ∏ x : (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ),
        (Polynomial.X - Polynomial.C (lpsOriginalCosetFractionRoot N hN x)) := by
  classical
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := Fintype.ofFinite (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  let Q := minpoly (FractionRing (Polynomial ℚ)) (lpsOriginalJNInFractionField N hN)
  let P := Q.map lpsOriginalJFractionEmbeddingQ
  have hP : P.Monic := (minpoly.monic (lpsOriginalJNInFractionField_integralQ N hN)).map _
  have hroot : ∀ x : (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ),
      P.eval (lpsOriginalCosetFractionRoot N hN x) = 0 := by
    intro x
    dsimp only [P]
    rw [Polynomial.eval_map]
    change Polynomial.aeval
      (lpsOriginalFractionPullbackQ x.out (lpsOriginalJNInFractionField N hN)) Q = 0
    exact lpsOriginalFractionPullback_minpolyRootQ N hN x.out
  have hd : P.natDegree = Fintype.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
    rw [Polynomial.natDegree_map]
    exact (lpsOriginalJNMinpolyDegreeQ N hN).trans Nat.card_eq_fintype_card
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (Polynomial.monic_prod_X_sub_C (lpsOriginalCosetFractionRoot N hN) Finset.univ) hP
  · exact Fintype.prod_dvd_of_coprime
      (Polynomial.pairwise_coprime_X_sub_C (lpsOriginalCosetFractionRoot_injective N hN))
      (fun x => Polynomial.dvd_iff_isRoot.mpr (hroot x))
  · rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ, hd]
end QEC.Coding.TannerLiftedProduct
