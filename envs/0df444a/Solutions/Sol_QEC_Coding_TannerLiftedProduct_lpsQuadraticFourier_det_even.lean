-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_det_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:52:18.636454+00:00
-- url     : https://prove2.me/submissions/4e7b7e10-5606-4154-bdf6-fa20fdc05a5b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_completeSquare
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_zero_eq_Gauss
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
theorem _root_.solution (N s : ℕ) [NeZero N] (a b d j : ℤ)
    (hdet : a*d-b*(N:ℤ)=1) :
    lpsQuadraticFourier N (((s:ℤ)*a:ℤ):ZMod N) ((2*(s:ℤ)*j:ℤ):ZMod N) =
      ZMod.stdAddChar (((-(s:ℤ)*d*j^2:ℤ):ZMod N))*lpsUnaryQuadraticGauss ((s:ℤ)*a) N := by
  have had : (a:ZMod N)*(d:ZMod N)=1 := by
    have h := congrArg (Int.cast : ℤ → ZMod N) hdet
    push_cast at h
    simpa using h
  have hn : ((2*(s:ℤ)*j:ℤ):ZMod N)=
      2*(((s:ℤ)*a:ℤ):ZMod N)*((d*j:ℤ):ZMod N) := by
    push_cast
    calc
      _ = 2*(s:ZMod N)*((a:ZMod N)*(d:ZMod N))*(j:ZMod N) := by rw [had];ring
      _ = _ := by ring
  change lpsQuadraticFourier N (((s:ℤ)*a:ℤ):ZMod N) ((2*(s:ℤ)*j:ℤ):ZMod N) = _
  rw [hn,lpsQuadraticFourier_completeSquare,lpsQuadraticFourier_zero_eq_Gauss]
  congr 2
  push_cast
  linear_combination -(s:ZMod N)*(d:ZMod N)*(j:ZMod N)^2*had
end QEC.Coding.TannerLiftedProduct
