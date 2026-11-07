-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2IntegerColumn_gcd_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:01:35.526091+00:00
-- url     : https://prove2.me/submissions/978d821e-d9d9-44c0-9e32-cd6fec8f5ec8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (M : GL (Fin 2) ℝ) (hd : 0<M.det.val)
    (a c : ℤ) (t : ℝ) (ha : M 0 0=(a:ℝ)/t) (hc : M 1 0=(c:ℝ)/t) :
    0<Int.gcd a c := by
  by_contra hn
  have hz : Int.gcd a c=0 := Nat.eq_zero_of_not_pos hn
  have hac : a=0 ∧ c=0 := by
    simpa only [Int.gcd_def,Int.natAbs_eq_zero] using Nat.gcd_eq_zero_iff.mp hz
  have hA : M 0 0=0 := by rw [ha,hac.1];simp
  have hC : M 1 0=0 := by rw [hc,hac.2];simp
  have hdet : M.det.val=0 := by
    change (M:Matrix (Fin 2) (Fin 2) ℝ).det=0
    simp [Matrix.det_fin_two,hA,hC]
  rw [hdet] at hd
  exact lt_irrefl _ hd
end QEC.Coding.TannerLiftedProduct
