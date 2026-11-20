-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_productLevelResidueRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:32:47.638289+00:00
-- url     : https://prove2.me/submissions/eaa91f3d-b3e1-4900-a073-be01790ad47f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralFricke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_productLevelNormalRoot
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_charPRoot_iff
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
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (h4N : 4 ∣ N) (hN : 0 < N)
    (A : Type*) [CommRing A] [IsDomain A] [Algebra (ZMod p) A]
    (q : lpsOriginalIntegerNormalZeroChart (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos) →+* A) :
    let j := q (lpsOriginalIntegerNormalZeroLevelPullback N (N*p)
      (dvd_mul_right N p) h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)
        (lpsOriginalIntegerNormalJN N hN))
    let y := q (lpsOriginalIntegerNormalJN (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos))
    y = j^p ∨ y^p = j := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)).toAlgebra
  let j := q (lpsOriginalIntegerNormalZeroLevelPullback N (N*p)
    (dvd_mul_right N p) h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)
      (lpsOriginalIntegerNormalJN N hN))
  let y := q (lpsOriginalIntegerNormalJN (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos))
  let f := lpsOriginalIntegerProductLevelCoefficientMap N p h4N hN (Fact.out : p.Prime).pos
  have hc : q.comp f = Polynomial.eval₂RingHom (Int.castRingHom A) j := by
    apply Polynomial.ringHom_ext
    · intro z
      have hz : Polynomial.C z = (z : Polynomial ℤ) := by
        simp
      rw [hz, map_intCast, map_intCast]
    · simp [f, j, lpsOriginalIntegerProductLevelCoefficientMap, lpsOriginalIntegerFrickeCoefficientMap, lpsOriginalIntegerNormalJN]
  have h := Polynomial.hom_eval₂
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos) f q
    (lpsOriginalIntegerNormalJN (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos))
  rw [lpsOriginalPrimeIntegerPolynomial_productLevelNormalRoot,
    map_zero, hc] at h
  exact (lpsOriginalPrimeIntegerPolynomial_charPRoot_iff p A j y).mp h.symm
end QEC.Coding.TannerLiftedProduct
