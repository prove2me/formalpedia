-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRationalRelation_holomorphicProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:55:43.802257+00:00
-- url     : https://prove2.me/submissions/4b0ccd42-cc02-4958-a3e4-d32e4ec2f8fb

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
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNMonicAnnihilatorUniqueQ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNMinpolyCosetProductQ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalRelation_fractionRoot
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbeddingQ_polynomial
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
    (N : ℕ) [NeZero N] (hN : 0 < N) (Φ : Polynomial (Polynomial ℚ))
    (hΦ : Φ.Monic)
    (hdeg : Φ.natDegree=Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))
    (hroot : ∀ τ : ℍ,
      Φ.eval₂ ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ))) (lpsOriginalJDilated N hN τ)=0) :
    letI := Fintype.ofFinite (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
    Φ.map lpsOriginalJHolomorphicEvalQ =
      ∏ x : (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ),
        (Polynomial.X-Polynomial.C
          (lpsOriginalHolomorphicPullback x.out (lpsOriginalJNHolomorphic N hN))) := by
  classical
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := Fintype.ofFinite (𝒮ℒ ⧸
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  have hm := lpsOriginalJNMonicAnnihilatorUniqueQ N hN
    (Φ.map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))))
    (hΦ.map _) (Polynomial.natDegree_map_le.trans hdeg.le)
    (lpsOriginalRationalRelation_fractionRoot N hN Φ hroot)
  have hc : lpsOriginalJFractionEmbeddingQ.comp
      (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))=
      (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
        lpsOriginalJHolomorphicEvalQ := by
    apply RingHom.ext
    intro P
    exact lpsOriginalJFractionEmbeddingQ_polynomial P
  have h := congrArg (Polynomial.map lpsOriginalJFractionEmbeddingQ) hm
  rw [Polynomial.map_map,hc,
    lpsOriginalJNMinpolyCosetProductQ N hN] at h
  apply Polynomial.map_injective
    (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
    (IsFractionRing.injective LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
  rw [Polynomial.map_map,Polynomial.map_prod]
  convert h using 1
  apply Finset.prod_congr rfl
  intro x _hx
  simp only [Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
    lpsOriginalCosetFractionRoot,lpsOriginalJNInFractionField,
    lpsOriginalFractionPullbackRing_localization]
end QEC.Coding.TannerLiftedProduct
