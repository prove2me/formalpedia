-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsSL2Z_firstColumn_gcd_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:50:06.86245+00:00
-- url     : https://prove2.me/submissions/f3a97486-e3c8-41bf-ae61-51bba61f9a45

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
theorem _root_.solution (γ : SL(2,ℤ)) : Int.gcd (γ 0 0) (γ 1 0)=1 := by
  let g := Int.gcd (γ 0 0) (γ 1 0)
  have hA : (g:ℤ)∣γ 0 0 := Int.gcd_dvd_left _ _
  have hC : (g:ℤ)∣γ 1 0 := Int.gcd_dvd_right _ _
  have hd : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have h := dvd_sub (dvd_mul_of_dvd_left hA (γ 1 1))
    (dvd_mul_of_dvd_left hC (γ 0 1))
  rw [mul_comm (γ 1 0) (γ 0 1),hd] at h
  exact Nat.dvd_one.mp (Int.ofNat_dvd_left.mp h)
end QEC.Coding.TannerLiftedProduct
