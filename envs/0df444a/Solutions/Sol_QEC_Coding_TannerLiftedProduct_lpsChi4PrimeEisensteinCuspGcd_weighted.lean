-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4PrimeEisensteinCuspGcd_weighted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:58:07.038105+00:00
-- url     : https://prove2.me/submissions/dd269370-c257-4393-8621-6a9d8eb5bb3e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrimeCuspShift_unit
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinCuspGcd_coprime_product
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
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) (r : Fin 4) (a : Fin q) :
    lpsChi4E2Character (r.val:ZMod 4)*lpsQuadraticE2Character q (a.val:ZMod q)*
      ((Int.gcd (((4*q:ℕ):ℤ)*γ 0 0+((q*r.val+4*a.val:ℕ):ℤ)*γ 1 0)
        (((4*q:ℕ):ℤ)*γ 1 0):ℂ)^2/((4*q:ℕ):ℂ)^2)=
      (lpsChi4E2Character (r.val:ZMod 4)*
        ((Int.gcd ((4:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((4:ℤ)*γ 1 0):ℂ)^2/(4:ℂ)^2))*
      (lpsQuadraticE2Character q (a.val:ZMod q)*
        ((Int.gcd ((q:ℤ)*γ 0 0+(a.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0):ℂ)^2/(q:ℂ)^2)) := by
  by_cases hr : IsUnit (r.val:ZMod 4)
  · by_cases ha : a=0
    · subst a
      simp only [Fin.val_zero,Nat.cast_zero,MulChar.map_zero,mul_zero,zero_mul]
    · have hrc := (ZMod.isUnit_iff_coprime r.val 4).mp hr
      have hrI : Int.gcd (r.val:ℤ) 4=1 := by
        change Nat.gcd r.val 4=1
        exact hrc.gcd_eq_one
      have hac := (lpsPrimeCuspShift_unit q a ha).coprime_dvd_right
        (dvd_pow_self q (by decide : (2:ℕ)≠0))
      have haI : Int.gcd (a.val:ℤ) (q:ℤ)=1 := by
        simpa only [Int.gcd_def,Int.natAbs_natCast] using hac.gcd_eq_one
      have hq4 := ((Fact.out : q.Prime).odd_of_ne_two hq2).coprime_two_right.pow_right 2
      have h4q : Int.gcd 4 (q:ℤ)=1 := by
        change Nat.gcd 4 q=1
        exact hq4.symm.gcd_eq_one
      have hg := lpsEisensteinCuspGcd_coprime_product 4 q γ r.val a.val h4q hrI haI
      have he : Int.gcd (((4*q:ℕ):ℤ)*γ 0 0+((q*r.val+4*a.val:ℕ):ℤ)*γ 1 0)
          (((4*q:ℕ):ℤ)*γ 1 0)=
          Int.gcd ((4:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((4:ℤ)*γ 1 0)*
            Int.gcd ((q:ℤ)*γ 0 0+(a.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0) := by
        simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hg
      rw [he]
      push_cast
      ring
  · rw [MulChar.map_nonunit lpsChi4E2Character hr]
    simp
end QEC.Coding.TannerLiftedProduct
