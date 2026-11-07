-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_integerThetaSeries_pow_four_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:35:54.095192+00:00
-- url     : https://prove2.me/submissions/60365319-9fed-4c03-908b-629c44cdd715

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (n : ℕ) :
    PowerSeries.coeff n (integerThetaSeries ^ 4) =
      Fintype.card (IntegerThetaFourWitness n) := by
  rw [show integerThetaSeries ^ 4 =
      ∏ _i : Fin 4, integerThetaSeries by simp]
  rw [PowerSeries.coeff_prod]
  simp only [coeff_integerThetaSeries, Fintype.card_sigma,
    Fintype.card_pi, Fintype.card_coe]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro l hl
  simp
end QEC.Coding.TannerLiftedProduct
