-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeToGenerated_base_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:25:27.21728+00:00
-- url     : https://prove2.me/submissions/72c38324-19ae-448d-bc4e-2d05620e035d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeRelativeMinpoly
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeRelativeAdjoinRootEquiv_base_coe
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
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N)
    (c : LPSOriginalGaussAffineOrder N hN p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN
      (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p) c)).val =
      (lpsOriginalGaussAffineToGenerated N hN p c).val := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let K := lpsOriginalGeneratedFunctionFieldQ N hN
  let P := lpsOriginalRelativeGaussHeckePolynomial N hN p
  let Q := lpsOriginalPrimeRelativeModularPolynomial N p hN (Fact.out : p.Prime).pos
  have h : Associated ((P.map (lpsOriginalGaussAffineToGenerated N hN p)).map
      (RingEquiv.refl K).toRingHom) Q :=
    Associated.of_eq (by simpa using (lpsOriginalRelativeGaussHeckePolynomial_fraction N p hN))
  change ((lpsOriginalPrimeRelativeAdjoinRootEquiv N p hNp h4N hN
    (AdjoinRoot.map (RingEquiv.refl K).toRingHom
      (P.map (lpsOriginalGaussAffineToGenerated N hN p)) Q h.symm.dvd
      (AdjoinRoot.map (lpsOriginalGaussAffineToGenerated N hN p) P
        (P.map (lpsOriginalGaussAffineToGenerated N hN p)) dvd_rfl
        (AdjoinRoot.of P c)))).val) = _
  rw [AdjoinRoot.map_of,AdjoinRoot.map_of]
  exact lpsOriginalPrimeRelativeAdjoinRootEquiv_base_coe N p hNp h4N hN _
end QEC.Coding.TannerLiftedProduct
