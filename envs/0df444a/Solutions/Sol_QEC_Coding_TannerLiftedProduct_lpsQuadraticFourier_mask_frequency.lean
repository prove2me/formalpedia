-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_mask_frequency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:52:19.798206+00:00
-- url     : https://prove2.me/submissions/bb8c3aa8-b009-442f-ae52-272e1df798fd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_completeSquare
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_zero_eq_Gauss
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N d k : ℕ) [NeZero N]
    (hN : N=4*d^2*k) (a b u j : ℤ) (hdet : a*u-b*(N:ℤ)=1) :
    lpsQuadraticFourier N (a:ZMod N) ((4*(d:ℤ)*(k:ℤ)*j:ℤ):ZMod N) =
      lpsUnaryQuadraticGauss a N := by
  have had : (a:ZMod N)*(u:ZMod N)=1 := by
    have h := congrArg (Int.cast : ℤ → ZMod N) hdet
    push_cast at h
    simpa using h
  let t : ZMod N := ((2*(d:ℤ)*(k:ℤ)*u*j:ℤ):ZMod N)
  have hn : ((4*(d:ℤ)*(k:ℤ)*j:ℤ):ZMod N)=2*(a:ZMod N)*t := by
    dsimp [t]
    push_cast
    linear_combination -(4:ZMod N)*(d:ZMod N)*(k:ZMod N)*(j:ZMod N)*had
  have hphase : -(a:ZMod N)*t^2=0 := by
    dsimp [t]
    push_cast
    calc
      _ = (-(a:ZMod N)*(k:ZMod N)*(u:ZMod N)^2*(j:ZMod N)^2)*(N:ZMod N) := by
        rw [hN]
        push_cast
        ring
      _ = 0 := by rw [ZMod.natCast_self,mul_zero]
  rw [hn,lpsQuadraticFourier_completeSquare,hphase,AddChar.map_zero_eq_one,one_mul,
    lpsQuadraticFourier_zero_eq_Gauss]
end QEC.Coding.TannerLiftedProduct
