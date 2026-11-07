-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGcdSquare_dvd_column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:53:24.771341+00:00
-- url     : https://prove2.me/submissions/bb6c97a6-0541-47d0-9d21-6ba8b517a577

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
theorem _root_.solution (N A C r : ℤ) (hr : Int.gcd r (N^2)=1) :
    (Int.gcd (N*A+r*C) (N^2):ℤ)∣N*C := by
  let d := Int.gcd (N*A+r*C) (N^2)
  have hx : (d:ℤ)∣N*A+r*C := Int.gcd_dvd_left _ _
  have hN : (d:ℤ)∣N^2 := Int.gcd_dvd_right _ _
  have hNd : d∣N.natAbs^2 := by
    simpa only [Int.natAbs_pow] using (Int.ofNat_dvd_left.mp hN)
  have hc0 : r.natAbs.Coprime (N.natAbs^2) := by
    simpa only [Int.gcd_def,Int.natAbs_pow] using hr
  have hc : Int.gcd (d:ℤ) r=1 := by
    simpa only [Int.gcd_def,Int.natAbs_natCast] using (hc0.coprime_dvd_right hNd).symm.gcd_eq_one
  have he : N*(N*A+r*C)-A*N^2=(N*C)*r := by ring
  have hh := dvd_sub (dvd_mul_of_dvd_right hx N) (dvd_mul_of_dvd_right hN A)
  rw [he] at hh
  exact Int.dvd_of_dvd_mul_left_of_gcd_one hh hc
end QEC.Coding.TannerLiftedProduct
