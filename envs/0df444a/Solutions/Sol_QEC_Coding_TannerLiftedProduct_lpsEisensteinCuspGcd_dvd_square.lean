-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEisensteinCuspGcd_dvd_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:52:12.64319+00:00
-- url     : https://prove2.me/submissions/014bcc70-a848-4d97-a111-7358a8c1be64

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
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
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℤ) (γ : SL(2,ℤ)) (r : ℤ) :
    Int.gcd (N*γ 0 0+r*γ 1 0) (N*γ 1 0) ∣ N.natAbs^2 := by
  let g := Int.gcd (N*γ 0 0+r*γ 1 0) (N*γ 1 0)
  have hA : (g:ℤ)∣N*γ 0 0+r*γ 1 0 := Int.gcd_dvd_left _ _
  have hC : (g:ℤ)∣N*γ 1 0 := Int.gcd_dvd_right _ _
  have hd : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have he : (N*γ 1 1)*(N*γ 0 0+r*γ 1 0)-
      (N*γ 0 1+r*γ 1 1)*(N*γ 1 0)=N^2 := by
    linear_combination N^2*hd
  have h := dvd_sub (dvd_mul_of_dvd_right hA (N*γ 1 1))
    (dvd_mul_of_dvd_right hC (N*γ 0 1+r*γ 1 1))
  rw [he] at h
  simpa only [Int.natAbs_pow] using (Int.ofNat_dvd_left.mp h)
end QEC.Coding.TannerLiftedProduct
