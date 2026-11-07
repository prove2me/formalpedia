-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticEisensteinCuspGcd_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:56:44.456813+00:00
-- url     : https://prove2.me/submissions/8cc2d00e-00ee-44ec-8aa0-730eb249e702

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
    (γ : SL(2,ℤ)) (r : Fin q) (hr : r≠0) (hC : ¬(q:ℤ)∣γ 1 0) :
    Int.gcd ((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0)=1 := by
  have hunit := lpsPrimeCuspShift_unit q r hr
  have hrc : (r.val:ZMod q)≠0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff r.val q).mp hz
    have hcq := hunit.coprime_dvd_right (dvd_pow_self q (by decide : (2:ℕ)≠0))
    exact ((Fact.out : q.Prime).coprime_iff_not_dvd.mp hcq.symm) hd
  have hc : (γ 1 0:ZMod q)≠0 := by
    intro hz
    exact hC ((ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) q).mp hz)
  have hx : ¬(q:ℤ)∣(q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0 := by
    intro hd
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hd
    have he : (((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0:ℤ):ZMod q)=
        (r.val:ZMod q)*(γ 1 0:ZMod q) := by push_cast;simp
    rw [he] at hz
    exact (mul_ne_zero hrc hc) hz
  have hx2 : ¬(q:ℤ)^2∣(q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0 := by
    intro hd
    exact hx ((dvd_pow_self (q:ℤ) (by decide : (2:ℕ)≠0)).trans hd)
  rw [lpsEisensteinCuspGcd_unit_reduce (q:ℤ) γ r.val (by simpa using hunit),
    lpsIntGcd_prime_sq,if_neg hx2,if_neg hx]
end QEC.Coding.TannerLiftedProduct
