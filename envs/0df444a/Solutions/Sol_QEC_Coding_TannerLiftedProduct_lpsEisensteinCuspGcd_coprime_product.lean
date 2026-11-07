-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEisensteinCuspGcd_coprime_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:57:02.957994+00:00
-- url     : https://prove2.me/submissions/7e01e488-c462-4f10-94a8-6c133cd1fa75

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinCuspGcd_unit_reduce
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGcdSquare_coprime_scale
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntGcd_coprime_mul
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
theorem _root_.solution (N M : ℤ) (γ : SL(2,ℤ)) (r s : ℤ)
    (hNM : Int.gcd N M=1) (hr : Int.gcd r N=1) (hs : Int.gcd s M=1) :
    Int.gcd ((N*M)*γ 0 0+(M*r+N*s)*γ 1 0) ((N*M)*γ 1 0)=
      Int.gcd (N*γ 0 0+r*γ 1 0) (N*γ 1 0)*
        Int.gcd (M*γ 0 0+s*γ 1 0) (M*γ 1 0) := by
  have hMN : Int.gcd M N=1 := by rw [Int.gcd_comm];exact hNM
  have htN : Int.gcd (M*r+N*s) N=1 := by
    rw [Int.gcd_add_mul_left_left,Int.gcd_mul_right_left_of_gcd_eq_one hMN,hr]
  have htM : Int.gcd (M*r+N*s) M=1 := by
    rw [add_comm,Int.gcd_add_mul_left_left,Int.gcd_mul_right_left_of_gcd_eq_one hNM,hs]
  have htNM : Int.gcd (M*r+N*s) (N*M)=1 := by
    have hN : (M*r+N*s).natAbs.Coprime N.natAbs := htN
    have hM : (M*r+N*s).natAbs.Coprime M.natAbs := htM
    simpa only [Int.gcd_def,Int.natAbs_mul] using (hN.mul_right hM).gcd_eq_one
  have htp := Int.gcd_pow_right_of_gcd_eq_one (k:=2) htNM
  have hrp := Int.gcd_pow_right_of_gcd_eq_one (k:=2) hr
  have hsp := Int.gcd_pow_right_of_gcd_eq_one (k:=2) hs
  have htC : (M*r+N*s).natAbs.Coprime ((N*M).natAbs^2) := by
    simpa only [Int.gcd_def,Int.natAbs_pow] using htp
  have hrC : r.natAbs.Coprime (N.natAbs^2) := by
    simpa only [Int.gcd_def,Int.natAbs_pow] using hrp
  have hsC : s.natAbs.Coprime (M.natAbs^2) := by
    simpa only [Int.gcd_def,Int.natAbs_pow] using hsp
  rw [lpsEisensteinCuspGcd_unit_reduce (N*M) γ (M*r+N*s) htC,
    lpsEisensteinCuspGcd_unit_reduce N γ r hrC,lpsEisensteinCuspGcd_unit_reduce M γ s hsC,
    mul_pow,lpsIntGcd_coprime_mul _ _ _ (Int.pow_gcd_pow_of_gcd_eq_one hNM)]
  have heN := lpsGcdSquare_coprime_scale N M (γ 0 0) (γ 1 0) r s hMN hr
  have heM := lpsGcdSquare_coprime_scale M N (γ 0 0) (γ 1 0) s r hNM hs
  rw [show M*N*γ 0 0+(M*r+N*s)*γ 1 0=(N*M)*γ 0 0+(M*r+N*s)*γ 1 0 by ring] at heN
  rw [show N*M*γ 0 0+(N*s+M*r)*γ 1 0=(N*M)*γ 0 0+(M*r+N*s)*γ 1 0 by ring] at heM
  rw [heN,heM]
end QEC.Coding.TannerLiftedProduct
