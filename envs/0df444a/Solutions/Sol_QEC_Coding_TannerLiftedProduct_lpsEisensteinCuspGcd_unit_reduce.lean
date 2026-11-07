-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEisensteinCuspGcd_unit_reduce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:54:13.74886+00:00
-- url     : https://prove2.me/submissions/c1c2a2bd-6825-4369-9932-962c36d4eb2f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinCuspGcd_dvd_square
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
theorem _root_.solution (N : ℤ) (γ : SL(2,ℤ)) (r : ℤ)
    (hr : r.natAbs.Coprime (N.natAbs^2)) :
    Int.gcd (N*γ 0 0+r*γ 1 0) (N*γ 1 0)=
      Int.gcd (N*γ 0 0+r*γ 1 0) (N^2) := by
  apply Nat.dvd_antisymm
  · apply Int.dvd_gcd (Int.gcd_dvd_left _ _)
    have h := lpsEisensteinCuspGcd_dvd_square N γ r
    exact Int.ofNat_dvd_left.mpr (by simpa only [Int.natAbs_pow] using h)
  · let d := Int.gcd (N*γ 0 0+r*γ 1 0) (N^2)
    have hx : (d:ℤ)∣N*γ 0 0+r*γ 1 0 := Int.gcd_dvd_left _ _
    have hN : (d:ℤ)∣N^2 := Int.gcd_dvd_right _ _
    have hNd : d∣N.natAbs^2 := by
      simpa only [Int.natAbs_pow] using (Int.ofNat_dvd_left.mp hN)
    have hc : Int.gcd (d:ℤ) r=1 := by
      simpa only [Int.gcd_def,Int.natAbs_natCast] using (hr.coprime_dvd_right hNd).symm.gcd_eq_one
    have he : N*(N*γ 0 0+r*γ 1 0)-γ 0 0*N^2=(N*γ 1 0)*r := by ring
    have hh := dvd_sub (dvd_mul_of_dvd_right hx N) (dvd_mul_of_dvd_right hN (γ 0 0))
    rw [he] at hh
    exact Int.dvd_gcd hx (Int.dvd_of_dvd_mul_left_of_gcd_one hh hc)
end QEC.Coding.TannerLiftedProduct
