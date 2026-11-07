-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4PrimeE2Twist_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:20:57.971215+00:00
-- url     : https://prove2.me/submissions/90207d4d-7c33-465c-afc3-47d6e73d4173

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2_real_shift_hasSum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Character_fin_fourier
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Gauss_ne_zero
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
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (z : ℍ) :
    HasSum (fun n : ℕ => -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q)*
      lpsChi4E2Character (n:ZMod 4)*Function.Periodic.qParam 1 (z:ℂ)^n)
      (lpsChi4PrimeE2Twist q z) := by
  classical
  have hs := hasSum_sum (s:=Finset.univ) (fun (r : Fin 4) hr =>
    (lpsQuadraticE2_real_shift_hasSum q hq2 (r.val:ℤ) z).mul_left
      (lpsChi4E2Character (r.val:ZMod 4)))
  have h := hs.mul_left (gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)))⁻¹
  change HasSum _ (lpsChi4PrimeE2Twist q z) at h
  apply h.congr_fun
  intro n
  have hf := lpsChi4E2Character_fin_fourier (n:ZMod 4)
  have hf' : (∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
      ZMod.stdAddChar ((((r.val:ℤ)*(n:ℤ)):ℤ):ZMod 4))=
      lpsChi4E2Character (n:ZMod 4)*gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)) := by
    simpa only [Int.cast_mul,Int.cast_natCast,mul_comm] using hf
  have he : (∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
      (-24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q)*
        ZMod.stdAddChar ((((r.val:ℤ)*(n:ℤ)):ℤ):ZMod 4)*Function.Periodic.qParam 1 (z:ℂ)^n))=
      (-24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q)*
        Function.Periodic.qParam 1 (z:ℂ)^n)*
      (∑ r : Fin 4,lpsChi4E2Character (r.val:ZMod 4)*
        ZMod.stdAddChar ((((r.val:ℤ)*(n:ℤ)):ℤ):ZMod 4)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [he,hf']
  field_simp [lpsChi4E2Gauss_ne_zero]
end QEC.Coding.TannerLiftedProduct
