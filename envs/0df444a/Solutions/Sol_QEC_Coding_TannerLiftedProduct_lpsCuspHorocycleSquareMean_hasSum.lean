-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleSquareMean_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:29:13.256878+00:00
-- url     : https://prove2.me/submissions/39e489b7-725e-4a55-b13b-df0c7e670135

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_parseval_nat
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycle_weight_exp
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    HasSum (fun n : ℕ => (lpsWeightTwoCusp_squareCoeff N f n:ℂ)*
      (Real.exp (-(4*Real.pi*(n:ℝ))*y):ℂ)) (lpsCuspHorocycleSquareMean N f y:ℂ) := by
  have h := lpsCuspHorocycleCircle_parseval_nat N f y hy
  have he (n : ℕ) : ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖^2*
      (Real.exp (-2*Real.pi*y))^(2*n)=
      lpsWeightTwoCusp_squareCoeff N f n*Real.exp (-(4*Real.pi*(n:ℝ))*y) := by
    rw [lpsCuspHorocycle_weight_exp]
    unfold lpsWeightTwoCusp_squareCoeff
    congr 2
    ring
  simp_rw [he] at h
  simpa only [Complex.ofReal_mul,lpsCuspHorocycleSquareMean] using hasSum_ofReal.mpr h
end QEC.Coding.TannerLiftedProduct
