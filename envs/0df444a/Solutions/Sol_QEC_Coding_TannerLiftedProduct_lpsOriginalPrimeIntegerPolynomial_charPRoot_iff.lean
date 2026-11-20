-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeIntegerPolynomial_charPRoot_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:26:50.743913+00:00
-- url     : https://prove2.me/submissions/3a970b3b-09d0-4940-8f22-c5958e6a61be

import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_Kronecker
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [IsDomain A]
    [Algebra (ZMod p) A] (j y : A) :
    (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom A) j) y = 0 ↔
      y = j^p ∨ y^p = j := by
  have hc : (Polynomial.eval₂RingHom (algebraMap (ZMod p) A) j).comp
      (Polynomial.mapRingHom (Int.castRingHom (ZMod p))) =
      Polynomial.eval₂RingHom (Int.castRingHom A) j := by
    apply Polynomial.ringHom_ext
    · intro z
      simp
    · simp
  rw [← hc, ← Polynomial.eval₂_map, lpsOriginalPrimeIntegerPolynomial_Kronecker]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.eval₂_pow, Polynomial.coe_eval₂RingHom, mul_eq_zero, sub_eq_zero]
end QEC.Coding.TannerLiftedProduct
