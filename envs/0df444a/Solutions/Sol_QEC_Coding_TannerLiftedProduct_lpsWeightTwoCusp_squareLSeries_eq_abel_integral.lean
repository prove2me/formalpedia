-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_squareLSeries_eq_abel_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:47:46.009194+00:00
-- url     : https://prove2.me/submissions/74c561d9-9ef2-40e5-aeac-62869debd5d8

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
    LSeries (fun n : ℕ => (lpsWeightTwoCusp_squareCoeff N f n:ℂ)) s=
      s*(∫ t in Set.Ioi (1:ℝ),
        (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (lpsWeightTwoCusp_squareCoeff N f n:ℂ))*
          (t:ℂ)^(-(s+1))) :=
  LSeries_eq_mul_integral_of_nonneg (lpsWeightTwoCusp_squareCoeff N f) (by norm_num) hs
    (lpsWeightTwoCusp_squareCoeff_sum_isBigO N f)
    (lpsWeightTwoCusp_squareCoeff_nonneg N f)
end QEC.Coding.TannerLiftedProduct
