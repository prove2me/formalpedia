-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEisensteinDilationCuspMatrix_prime_pow_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:05:43.610263+00:00
-- url     : https://prove2.me/submissions/5db2d0ac-68d0-41b3-b4f6-ce2000c2dd2b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinDilationCuspMatrix_column
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
theorem _root_.solution (p m : ℕ) (hm : 0<m)
    (hmp : m.Coprime p) (γ : SL(2,ℤ)) (e : ℕ) :
    (p:ℤ)^e∣γ 1 0 ↔ (p:ℤ)^e∣lpsEisensteinDilationCuspMatrix m hm γ 1 0 := by
  have hd : Int.gcd (m:ℤ) (γ 1 0)∣m := by
    simpa only [Int.natAbs_natCast] using
      (Int.ofNat_dvd_left.mp (Int.gcd_dvd_left (m:ℤ) (γ 1 0)))
  have hc := (hmp.coprime_dvd_left hd).symm.pow_left e
  have hI : Int.gcd ((p:ℤ)^e) (Int.gcd (m:ℤ) (γ 1 0):ℤ)=1 := by
    simpa only [Int.gcd_def,Int.natAbs_pow,Int.natAbs_natCast] using hc.gcd_eq_one
  have hcol := (lpsEisensteinDilationCuspMatrix_column m hm γ).2
  constructor
  · intro h
    rw [hcol] at h
    exact Int.dvd_of_dvd_mul_right_of_gcd_one h hI
  · intro h
    rw [hcol]
    exact dvd_mul_of_dvd_right h _
end QEC.Coding.TannerLiftedProduct
