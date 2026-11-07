-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsUnaryQuadraticGauss_square_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:54:25.573847+00:00
-- url     : https://prove2.me/submissions/dc4d2512-2f6a-4208-926e-0fa836dca2a1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_mask_frequency
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticGauss_mask_sum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N d k : ℕ) [NeZero N]
    (hN : N=4*d^2*k) (hd : 0 < d) (hk : 0 < k)
    (a b u : ℤ) (hdet : a*u-b*(N:ℤ)=1) :
    lpsUnaryQuadraticGauss (a*(d:ℤ)^2) N =
      (d:ℂ)*lpsUnaryQuadraticGauss a N := by
  let m := 4*d*k
  have hm : 0 < m := by dsimp [m];positivity
  let : NeZero d := ⟨ne_of_gt hd⟩
  let : NeZero m := ⟨ne_of_gt hm⟩
  have hNm : N=d*m := by dsimp [m];rw [hN];ring
  have hdetm : a*u-b*((d*m:ℕ):ℤ)=1 := by rw [← hNm];exact hdet
  have hmask := lpsQuadraticGauss_mask_sum d m a
  have hf (j : Fin d) :
      lpsQuadraticFourier (d*m) (a:ZMod (d*m)) (((m:ℤ)*j.val:ℤ):ZMod (d*m)) =
        lpsUnaryQuadraticGauss a (d*m) := by
    have h := lpsQuadraticFourier_mask_frequency (d*m) d k (hNm.symm.trans hN) a b u j.val hdetm
    simpa only [m,Nat.cast_mul,Nat.cast_ofNat] using h
  simp_rw [hf] at hmask
  rw [hNm]
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hmask.symm
end QEC.Coding.TannerLiftedProduct
