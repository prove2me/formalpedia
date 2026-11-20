-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaSquareCoeff_eq_trace_sub_correction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:50:48.835655+00:00
-- url     : https://prove2.me/submissions/55e2c187-4807-4ce4-bcc6-2b56d30ce44d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaSquareMean
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsThetaCuspidalRemainder


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (n : ℕ) :
    lpsThetaSquareCoeff q hq4 n=
      ‖((PowerSeries.coeff n (lpsTraceThetaSeries q):ℕ):ℂ)-
        lpsThetaEisensteinCorrectionCoefficient q n‖^2 := by
  unfold lpsThetaSquareCoeff lpsWeightTwoCusp_squareCoeff
  rw [coeff_qExpansion_lpsThetaCuspidalRemainder]
end QEC.Coding.TannerLiftedProduct
