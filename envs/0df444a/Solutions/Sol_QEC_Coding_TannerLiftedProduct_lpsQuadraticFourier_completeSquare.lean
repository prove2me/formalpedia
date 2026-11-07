-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticFourier_completeSquare
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:44:43.751139+00:00
-- url     : https://prove2.me/submissions/1396ea0c-1c93-4af0-a020-67c556748a60

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCharacteristics
import Mathlib.Analysis.Fourier.ZMod
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaFourier
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
theorem _root_.solution (N : ℕ) [NeZero N] (a t : ZMod N) :
    lpsQuadraticFourier N a (2*a*t) =
      ZMod.stdAddChar (-a*t^2) * lpsQuadraticFourier N a 0 := by
  unfold lpsQuadraticFourier
  rw [Finset.mul_sum]
  have h := Equiv.sum_comp (Equiv.addRight t) (fun r : ZMod N => ZMod.stdAddChar (-a*t^2) * ZMod.stdAddChar (a*r^2+0*r))
  rw [← h]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [Equiv.coe_addRight]
  ring
end QEC.Coding.TannerLiftedProduct
