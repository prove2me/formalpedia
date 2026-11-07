-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_fractionProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:12:22.712675+00:00
-- url     : https://prove2.me/submissions/f43e7a37-dfa2-494b-8a78-ed268f2d3f07

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeModularBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_degree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_holomorphicBranchRoot
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeFractionBranch_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJHolomorphicEvalZ_injective
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
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
      ((algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
        lpsOriginalJHolomorphicEvalZ)=
      ∏ i : Option (Fin p), (Polynomial.X-Polynomial.C (lpsOriginalPrimeFractionBranch p i)) := by
  classical
  let f:=algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
  let P:=(lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
    (f.comp lpsOriginalJHolomorphicEvalZ)
  have hP:P.Monic:=(lpsOriginalIntegerPolynomial_monic p (Fact.out : p.Prime).pos).map _
  have hr (i : Option (Fin p)) : P.eval (lpsOriginalPrimeFractionBranch p i)=0 := by
    rw [Polynomial.eval_map]
    change Polynomial.eval₂ (f.comp lpsOriginalJHolomorphicEvalZ)
      (f (lpsOriginalPrimeBranchHolomorphic p i))
      (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos)=0
    rw [← Polynomial.hom_eval₂,lpsOriginalPrimeIntegerPolynomial_holomorphicBranchRoot,map_zero]
  have hd:P.natDegree=p+1 := by
    dsimp only [P]
    have hf : Function.Injective (f.comp lpsOriginalJHolomorphicEvalZ) := by
      intro P Q h
      exact lpsOriginalJHolomorphicEvalZ_injective
        ((IsFractionRing.injective LPSOriginalHolomorphicRing
          LPSOriginalHolomorphicFractionField) h)
    rw [Polynomial.natDegree_map_eq_of_injective hf,
      lpsOriginalPrimeIntegerPolynomial_degree]
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (Polynomial.monic_prod_X_sub_C (lpsOriginalPrimeFractionBranch p) Finset.univ) hP
  · exact Fintype.prod_dvd_of_coprime
      (Polynomial.pairwise_coprime_X_sub_C (lpsOriginalPrimeFractionBranch_injective p))
      (fun i=>Polynomial.dvd_iff_isRoot.mpr (hr i))
  · rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card,Finset.card_univ,hd]
    simp
end QEC.Coding.TannerLiftedProduct
