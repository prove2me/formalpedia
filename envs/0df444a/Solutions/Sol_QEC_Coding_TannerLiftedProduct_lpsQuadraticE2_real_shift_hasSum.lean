-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2_real_shift_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:16:32.145411+00:00
-- url     : https://prove2.me/submissions/d62d8051-ac0f-474c-b85a-307f1cd45d52

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIteratedEisenstein
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQParam_real_shift
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_hasSum
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
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (a : ℤ) (z : ℍ) :
    HasSum (fun n : ℕ => -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q)*
      ZMod.stdAddChar (((a*(n:ℤ)):ℤ):ZMod 4)*Function.Periodic.qParam 1 (z:ℂ)^n)
      (lpsQuadraticE2Twist q (((a:ℝ)/4) +ᵥ z)) := by
  have h := lpsQuadraticE2Twist_hasSum q hq2 (((a:ℝ)/4) +ᵥ z)
  convert h using 1
  ext n
  have hshift := lpsQParam_real_shift 4 a z
  norm_num only [Nat.cast_ofNat] at hshift
  rw [hshift,mul_pow]
  have hc := AddChar.map_nsmul_eq_pow (ZMod.stdAddChar (N:=4)) n (a:ZMod 4)
  simp only [nsmul_eq_mul,Int.cast_mul,Int.cast_natCast] at hc ⊢
  rw [←hc]
  ring
end QEC.Coding.TannerLiftedProduct
