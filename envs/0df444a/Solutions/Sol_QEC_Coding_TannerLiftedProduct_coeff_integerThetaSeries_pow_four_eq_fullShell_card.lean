-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coeff_integerThetaSeries_pow_four_eq_fullShell_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:37:18.255016+00:00
-- url     : https://prove2.me/submissions/5608f7b4-3161-4cfb-8854-3065c513ade7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_integerThetaSeries_pow_four_eq_card

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {n : ℕ} (hn : 0 < n) :
    PowerSeries.coeff n (integerThetaSeries ^ 4) =
      (lpsQuaternionFullShell n).card := by
  calc
    PowerSeries.coeff n (integerThetaSeries ^ 4) =
        Fintype.card (IntegerThetaFourWitness n) :=
      coeff_integerThetaSeries_pow_four_eq_card n
    _ = Fintype.card {t // t ∈ lpsQuaternionFullShell n} :=
      Fintype.card_congr (integerThetaFourWitnessEquivFullShell hn)
    _ = (lpsQuaternionFullShell n).card := Fintype.card_coe _
end QEC.Coding.TannerLiftedProduct
