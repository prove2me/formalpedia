-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_squareCoeff_div_rpow_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:29:07.780871+00:00
-- url     : https://prove2.me/submissions/ba4d4e39-eadc-48d0-9ac1-4955c1c273a3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_squareCoeff_nonneg
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_squareCoeff_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_squareLSeries_summable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (s : ℂ) (hs : 2<s.re) :
    Summable (fun n : ℕ => lpsWeightTwoCusp_squareCoeff N f n/(n:ℝ)^s.re) := by
  have h := (lpsWeightTwoCusp_squareLSeries_summable N f s hs).norm
  apply h.congr
  intro n
  rw [LSeries.norm_term_eq]
  by_cases hn : n=0
  · subst n
    simp [lpsWeightTwoCusp_squareCoeff_zero]
  · rw [if_neg hn,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (lpsWeightTwoCusp_squareCoeff_nonneg N f n)]
end QEC.Coding.TannerLiftedProduct
