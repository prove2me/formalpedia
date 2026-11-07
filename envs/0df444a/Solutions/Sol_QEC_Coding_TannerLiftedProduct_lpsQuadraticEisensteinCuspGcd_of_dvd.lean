-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticEisensteinCuspGcd_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:56:51.066972+00:00
-- url     : https://prove2.me/submissions/87d99367-d46d-4b95-b36f-fd75b444ff11

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinCuspGcd_unit_reduce
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntGcd_prime_sq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrimeCuspShift_unit
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
theorem _root_.solution (q : ℕ) [Fact q.Prime]
    (γ : SL(2,ℤ)) (r : Fin q) (hr : r≠0) (D : ℤ) (hC : γ 1 0=(q:ℤ)*D) :
    Int.gcd ((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0)=
      if (((γ 0 0+(r.val:ℤ)*D):ℤ):ZMod q)=0 then q^2 else q := by
  have hunit := lpsPrimeCuspShift_unit q r hr
  have hq : (q:ℤ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have he : (q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0=(q:ℤ)*(γ 0 0+(r.val:ℤ)*D) := by
    rw [hC];ring
  have hd : (q:ℤ)∣(q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0 := by
    rw [he];exact dvd_mul_right _ _
  have hd2 : (q:ℤ)^2∣(q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0 ↔
      (((γ 0 0+(r.val:ℤ)*D):ℤ):ZMod q)=0 := by
    rw [he,pow_two,mul_dvd_mul_iff_left hq]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).symm
  rw [lpsEisensteinCuspGcd_unit_reduce (q:ℤ) γ r.val (by simpa using hunit),
    lpsIntGcd_prime_sq]
  by_cases hz : (((γ 0 0+(r.val:ℤ)*D):ℤ):ZMod q)=0
  · rw [if_pos (hd2.mpr hz),if_pos hz]
  · rw [if_neg (fun h => hz (hd2.mp h)),if_pos hd,if_neg hz]
end QEC.Coding.TannerLiftedProduct
