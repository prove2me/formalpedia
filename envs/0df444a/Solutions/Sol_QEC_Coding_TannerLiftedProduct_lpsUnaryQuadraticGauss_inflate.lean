-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_inflate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:48:44.782355+00:00
-- url     : https://prove2.me/submissions/67d379ef-2434-4e1a-ba7b-c874fa7724bd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_inflate_modulus
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_sum_blocks
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFin_cast_finEquiv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_zero_eq_Gauss
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (m n : ℕ) [NeZero m] [NeZero n]
    (a : ℤ) :
    lpsUnaryQuadraticGauss (a*(m:ℤ)) (m*n) =
      (m:ℂ)*lpsUnaryQuadraticGauss a n := by
  classical
  rw [← lpsQuadraticFourier_zero_eq_Gauss,lpsQuadraticFourier,lpsZMod_sum_blocks]
  simp only [zero_mul,add_zero]
  have h (i : Fin m) (r : Fin n) :
      ZMod.stdAddChar ((((a*(m:ℤ)):ℤ):ZMod (m*n))*((r.val+n*i.val:ℕ):ZMod (m*n))^2) =
        ZMod.stdAddChar ((a:ZMod n)*(r.val:ZMod n)^2) := by
    have he : (((a*(m:ℤ)):ℤ):ZMod (m*n))*((r.val+n*i.val:ℕ):ZMod (m*n))^2 =
        (((m:ℤ)*(a*(r.val:ℤ)^2):ℤ):ZMod (m*n)) := by
      have hz : ((m*n:ℕ):ZMod (m*n))=0 := ZMod.natCast_self _
      push_cast at hz ⊢
      linear_combination (a:ZMod (m*n))*(i.val:ZMod (m*n))*
        (2*(r.val:ZMod (m*n))+(n:ZMod (m*n))*(i.val:ZMod (m*n)))*hz
    rw [he]
    have hi := lpsChar_inflate_modulus (m*n) n m (Nat.mul_comm _ _) (a*(r.val:ℤ)^2)
    simpa only [Int.cast_mul,Int.cast_pow,Int.cast_natCast] using hi
  simp_rw [h]
  rw [Finset.sum_const]
  simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  congr 1
  rw [← lpsQuadraticFourier_zero_eq_Gauss,lpsQuadraticFourier]
  apply Fintype.sum_equiv (ZMod.finEquiv n).toEquiv
  intro r
  simp only [zero_mul,add_zero]
  change ZMod.stdAddChar ((a:ZMod n)*(r.val:ZMod n)^2) =
    ZMod.stdAddChar ((a:ZMod n)*(ZMod.finEquiv n r)^2)
  rw [← lpsFin_cast_finEquiv]
end QEC.Coding.TannerLiftedProduct
