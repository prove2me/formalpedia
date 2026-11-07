-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:20:56.53722+00:00
-- url     : https://prove2.me/submissions/bf6be1ef-c2da-4c48-909e-ada27e281b4c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Character_values
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Gauss_ne_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Character_fin_fourier
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2_real_shift_hasSum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (z : ℍ) :
    HasSum (fun n : ℕ => -24*(ArithmeticFunction.sigma 1 n:ℂ) *
      lpsChi4E2Character (n:ZMod 4) * Function.Periodic.qParam 1 (z:ℂ)^n)
      (lpsChi4E2Twist z) := by
  classical
  have hsum := hasSum_sum (s:=Finset.univ) (fun (a : Fin 4) ha =>
    (lpsE2_real_shift_hasSum 4 (a.val:ℤ) z).mul_left
      (lpsChi4E2Character (a.val:ZMod 4)))
  have h := hsum.mul_left (gaussSum (lpsChi4E2Character) (ZMod.stdAddChar (N:=4)))⁻¹
  change HasSum _ (lpsChi4E2Twist z) at h
  convert h using 1
  ext n
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  rw [show (∑ a : Fin 4, lpsChi4E2Character (a.val:ZMod 4) *
    (if n=0 then 1 else -24*ArithmeticFunction.sigma 1 n:ℂ) *
    ZMod.stdAddChar ((((a.val:ℤ)*(n:ℤ)):ℤ):ZMod 4)) =
    (if n=0 then 1 else -24*ArithmeticFunction.sigma 1 n:ℂ) *
    (∑ a : Fin 4, lpsChi4E2Character (a.val:ZMod 4)*
      ZMod.stdAddChar ((((a.val:ℤ)*(n:ℤ)):ℤ):ZMod 4)) by
        rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro a ha;ring]
  have hfour := lpsChi4E2Character_fin_fourier (n:ZMod 4)
  have hfour' : (∑ a : Fin 4,lpsChi4E2Character (a.val:ZMod 4)*
    ZMod.stdAddChar ((((a.val:ℤ)*(n:ℤ)):ℤ):ZMod 4))=
    lpsChi4E2Character (n:ZMod 4)*gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)) := by
      simpa only [Int.cast_mul,Int.cast_natCast,mul_comm] using hfour
  rw [hfour']
  by_cases hn : n=0
  · subst n
    simp [lpsChi4E2Character_values.1]
  · simp only [if_neg hn]
    have hg := lpsChi4E2Gauss_ne_zero
    field_simp [hg]
end QEC.Coding.TannerLiftedProduct
