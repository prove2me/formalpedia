-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticGauss_scaled_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:52:26.004274+00:00
-- url     : https://prove2.me/submissions/dea1b57e-5011-44cb-9eaf-9557d2f3cb7f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussSquare
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_sum_blocks
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadratic_scaled_period
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticFourier_zero_eq_Gauss
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Real
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (d m : ℕ) [NeZero d] [NeZero m]
    (a : ℤ) :
    lpsUnaryQuadraticGauss (a*(d:ℤ)^2) (d*m) =
      (d:ℂ) * ∑ r : Fin m,
        ZMod.stdAddChar (((a*(d:ℤ)^2*(r.val:ℤ)^2):ℤ):ZMod (d*m)) := by
  classical
  rw [← lpsQuadraticFourier_zero_eq_Gauss,lpsQuadraticFourier,lpsZMod_sum_blocks]
  simp only [zero_mul,add_zero]
  have h (i : Fin d) (r : Fin m) :
      ZMod.stdAddChar ((((a*(d:ℤ)^2):ℤ):ZMod (d*m))*((r.val+m*i.val:ℕ):ZMod (d*m))^2) =
      ZMod.stdAddChar (((a*(d:ℤ)^2*(r.val:ℤ)^2):ℤ):ZMod (d*m)) := by
    have he := lpsQuadratic_scaled_period d m a r.val i.val
    convert he using 1
    push_cast
    rfl
  simp_rw [h]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
end QEC.Coding.TannerLiftedProduct
