-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGcdSquare_coprime_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:55:26.595758+00:00
-- url     : https://prove2.me/submissions/069f17ac-e7da-4635-9268-8f37a18200a4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGcdSquare_dvd_column
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
theorem _root_.solution (N M A C r s : ℤ)
    (hM : Int.gcd M N=1) (hr : Int.gcd r N=1) :
    Int.gcd (M*N*A+(M*r+N*s)*C) (N^2)=Int.gcd (N*A+r*C) (N^2) := by
  have ht : Int.gcd (M*r+N*s) N=1 := by
    rw [Int.gcd_add_mul_left_left,Int.gcd_mul_right_left_of_gcd_eq_one hM,hr]
  have hMp := Int.gcd_pow_right_of_gcd_eq_one (k:=2) hM
  have hrp := Int.gcd_pow_right_of_gcd_eq_one (k:=2) hr
  have htp := Int.gcd_pow_right_of_gcd_eq_one (k:=2) ht
  have hyC := lpsGcdSquare_dvd_column N A C r hrp
  have hxC := lpsGcdSquare_dvd_column N (M*A) C (M*r+N*s) htp
  rw [show N*(M*A)=M*N*A by ring] at hxC
  have he : M*N*A+(M*r+N*s)*C=M*(N*A+r*C)+s*(N*C) := by ring
  apply Nat.dvd_antisymm
  · let d := Int.gcd (M*N*A+(M*r+N*s)*C) (N^2)
    have hx : (d:ℤ)∣M*N*A+(M*r+N*s)*C := Int.gcd_dvd_left _ _
    have hN : (d:ℤ)∣N^2 := Int.gcd_dvd_right _ _
    have hNd : d∣N.natAbs^2 := by
      simpa only [Int.natAbs_pow] using (Int.ofNat_dvd_left.mp hN)
    have hc0 : M.natAbs.Coprime (N.natAbs^2) := by
      simpa only [Int.gcd_def,Int.natAbs_pow] using hMp
    have hc : Int.gcd (d:ℤ) M=1 := by
      simpa only [Int.gcd_def,Int.natAbs_natCast] using (hc0.coprime_dvd_right hNd).symm.gcd_eq_one
    have hmul := dvd_sub hx (dvd_mul_of_dvd_right hxC s)
    rw [he,add_sub_cancel_right] at hmul
    exact Int.dvd_gcd (Int.dvd_of_dvd_mul_right_of_gcd_one hmul hc) hN
  · apply Int.dvd_gcd
    · rw [he]
      exact dvd_add (dvd_mul_of_dvd_right (Int.gcd_dvd_left _ _) M)
        (dvd_mul_of_dvd_right hyC s)
    · exact Int.gcd_dvd_right _ _
end QEC.Coding.TannerLiftedProduct
