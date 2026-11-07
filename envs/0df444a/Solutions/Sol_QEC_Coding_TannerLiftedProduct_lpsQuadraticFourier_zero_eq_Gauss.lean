-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_zero_eq_Gauss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:47:19.334408+00:00
-- url     : https://prove2.me/submissions/34d40d84-40d6-42a4-8d11-963afbf02a8f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticPhase_stdAddChar
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
theorem _root_.solution (N : ℕ) [NeZero N] (a : ℤ) :
    lpsQuadraticFourier N (a:ZMod N) 0 = lpsUnaryQuadraticGauss a N := by
  unfold lpsQuadraticFourier lpsUnaryQuadraticGauss
  symm
  apply Fintype.sum_equiv (ZMod.finEquiv N).toEquiv
  intro r
  simp only [zero_mul,add_zero]
  exact lpsQuadraticPhase_stdAddChar N a r
end QEC.Coding.TannerLiftedProduct
