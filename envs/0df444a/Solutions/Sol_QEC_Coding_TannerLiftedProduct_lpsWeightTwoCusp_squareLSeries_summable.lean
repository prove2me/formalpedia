-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_squareLSeries_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:19:33.751384+00:00
-- url     : https://prove2.me/submissions/ceb15aaf-9b01-41de-9eac-bbdde6c369f7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_squareCoeff_nonneg
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_squareCoeff_sum_isBigO

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (s : ℂ) (hs : 2<s.re) :
    LSeriesSummable (fun n : ℕ => (lpsWeightTwoCusp_squareCoeff N f n:ℂ)) s :=
  LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (lpsWeightTwoCusp_squareCoeff_sum_isBigO N f)
    (lpsWeightTwoCusp_squareCoeff_nonneg N f) (by norm_num) hs
end QEC.Coding.TannerLiftedProduct
