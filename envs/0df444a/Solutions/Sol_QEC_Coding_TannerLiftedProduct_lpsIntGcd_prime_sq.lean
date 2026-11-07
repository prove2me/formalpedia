-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIntGcd_prime_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:50:44.586189+00:00
-- url     : https://prove2.me/submissions/8f517dfd-bfa5-49eb-837d-16c03a09f5e8

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
theorem _root_.solution (q : ℕ) [Fact q.Prime] (x : ℤ) :
    Int.gcd x ((q:ℤ)^2)=
      if (q:ℤ)^2∣x then q^2 else if (q:ℤ)∣x then q else 1 := by
  by_cases h2 : (q:ℤ)^2∣x
  · rw [if_pos h2,Int.gcd_eq_natAbs_right h2]
    simp
  · rw [if_neg h2]
    by_cases h1 : (q:ℤ)∣x
    · rw [if_pos h1]
      obtain ⟨y,rfl⟩ := h1
      have hy : ¬q∣y.natAbs := by
        intro hd
        obtain ⟨t,ht⟩ := Int.ofNat_dvd_left.mpr hd
        exact h2 ⟨t,by rw [ht];ring⟩
      have hc : Int.gcd y (q:ℤ)=1 := by
        simpa only [Int.gcd_def,Int.natAbs_natCast] using
          ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr hy).symm.gcd_eq_one
      rw [pow_two,Int.gcd_mul_left,hc]
      simp
    · rw [if_neg h1]
      have hx : ¬q∣x.natAbs := by
        intro hd
        exact h1 (Int.ofNat_dvd_left.mpr hd)
      simpa only [Int.gcd_def,Int.natAbs_pow,Int.natAbs_natCast] using
        ((Fact.out : q.Prime).coprime_pow_of_not_dvd (m:=2) hx).gcd_eq_one
end QEC.Coding.TannerLiftedProduct
