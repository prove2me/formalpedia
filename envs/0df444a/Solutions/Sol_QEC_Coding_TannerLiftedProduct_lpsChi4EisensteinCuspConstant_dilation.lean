-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4EisensteinCuspConstant_dilation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:34:34.815141+00:00
-- url     : https://prove2.me/submissions/99f39a6f-9076-44cd-a921-77bc280b3c67

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinDilationCuspMatrix_column
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinDilationCuspMatrix_prime_pow_dvd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsInt_mod_eight_four_iff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Character_square
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
theorem _root_.solution (m : ℕ) (hm : 0<m)
    (hm4 : m.Coprime 4) (γ : SL(2,ℤ)) :
    lpsChi4EisensteinCuspConstant (lpsEisensteinDilationCuspMatrix m hm γ)=
      lpsChi4E2Character (m:ZMod 4)*lpsChi4EisensteinCuspConstant γ := by
  let δ := lpsEisensteinDilationCuspMatrix m hm γ
  let d : ℕ := Int.gcd (m:ℤ) (γ 1 0)
  have hcol : (m:ℤ)*γ 0 0=(d:ℤ)*δ 0 0 ∧ γ 1 0=(d:ℤ)*δ 1 0 :=
    lpsEisensteinDilationCuspMatrix_column m hm γ
  have hd : d∣m := by
    simpa only [Int.natAbs_natCast] using
      (Int.ofNat_dvd_left.mp (Int.gcd_dvd_left (m:ℤ) (γ 1 0)))
  have hd4 : IsUnit (d:ZMod 4) :=
    (ZMod.isUnit_iff_coprime d 4).mpr (hm4.coprime_dvd_left hd)
  have hm2 : m.Coprime 2 := hm4.coprime_dvd_right (by decide : (2:ℕ)∣4)
  have h4 := lpsEisensteinDilationCuspMatrix_prime_pow_dvd 2 m hm hm2 γ 2
  have h8 := lpsEisensteinDilationCuspMatrix_prime_pow_dvd 2 m hm hm2 γ 3
  norm_num only [Int.reducePow] at h4 h8
  change (4:ℤ)∣γ 1 0 ↔ (4:ℤ)∣δ 1 0 at h4
  change (8:ℤ)∣γ 1 0 ↔ (8:ℤ)∣δ 1 0 at h8
  have hs : γ 1 0%8=4 ↔ δ 1 0%8=4 := by
    rw [lpsInt_mod_eight_four_iff,lpsInt_mod_eight_four_iff,h4,h8]
  change lpsChi4EisensteinCuspConstant δ=_
  unfold lpsChi4EisensteinCuspConstant
  by_cases hC : γ 1 0%8=4
  · rw [if_pos hC,if_pos (hs.mp hC)]
    have hδC := (lpsInt_mod_eight_four_iff (δ 1 0)).mp (hs.mp hC)
    have hDD : γ 1 0/4=(d:ℤ)*(δ 1 0/4) := by
      calc
        γ 1 0/4=((d:ℤ)*δ 1 0)/4 := congrArg (·/4) hcol.2
        _=(d:ℤ)*(δ 1 0/4) := Int.mul_ediv_assoc _ hδC.1
    have hx : (m:ℤ)*(γ 0 0*(γ 1 0/4))=(d:ℤ)^2*(δ 0 0*(δ 1 0/4)) := by
      calc
        (m:ℤ)*(γ 0 0*(γ 1 0/4))=((m:ℤ)*γ 0 0)*(γ 1 0/4) := by ring
        _=((d:ℤ)*δ 0 0)*((d:ℤ)*(δ 1 0/4)) := congrArg₂ (·*·) hcol.1 hDD
        _=(d:ℤ)^2*(δ 0 0*(δ 1 0/4)) := by ring
    have hF : (m:ZMod 4)*(((γ 0 0*(γ 1 0/4)):ℤ):ZMod 4)=
        (d:ZMod 4)^2*(((δ 0 0*(δ 1 0/4)):ℤ):ZMod 4) := by
      have h := congrArg (fun x : ℤ => (x:ZMod 4)) hx
      simpa only [Int.cast_mul,Int.cast_natCast,Int.cast_pow] using h
    have hc := congrArg lpsChi4E2Character hF
    rw [map_mul,map_mul,lpsChi4E2Character_square _ hd4,one_mul] at hc
    rw [←hc]
    ring
  · rw [if_neg hC,if_neg (fun h => hC (hs.mpr h)),mul_zero]
end QEC.Coding.TannerLiftedProduct
