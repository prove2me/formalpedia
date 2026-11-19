-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticEisensteinCuspConstant_of_column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:51:10.644179+00:00
-- url     : https://prove2.me/submissions/879abafa-17b7-402c-9016-8f123343c499

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Character_neg_div
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPrimePowerCusp_denominator_dvd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsStandardThetaModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsStandardThetaModularForm_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q v L : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (hc : q.Coprime L) (γ : SL(2,ℤ)) (hC : γ 1 0=((q^v*L:ℕ):ℤ)) :
    lpsQuadraticEisensteinCuspConstant q γ=
      if v=1 then ((q:ℂ)^2-1)/gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q))*
        lpsQuadraticE2Character q (((γ 0 0*(L:ℤ)):ℤ):ZMod q) else 0 := by
  have h1 := lpsPrimePowerCusp_denominator_dvd q 1 v L (Fact.out : q.Prime) hc
  have h2 := lpsPrimePowerCusp_denominator_dvd q 2 v L (Fact.out : q.Prime) hc
  simp only [pow_one] at h1
  have h1C : (q:ℤ)∣γ 1 0 ↔ 1≤v := by simpa only [hC] using h1
  have h2C : (q:ℤ)^2∣γ 1 0 ↔ 2≤v := by simpa only [hC] using h2
  unfold lpsQuadraticEisensteinCuspConstant
  simp_rw [h1C,h2C]
  by_cases hv : v=1
  · subst v
    have hdiv : γ 1 0/(q:ℤ)=(L:ℤ) := by
      rw [hC,pow_one,Nat.cast_mul]
      exact Int.mul_ediv_cancel_left _ (by exact_mod_cast (Fact.out : q.Prime).ne_zero)
    rw [if_pos (by omega),if_neg (by omega),if_pos rfl,hdiv,
      lpsQuadraticE2Character_neg_div q hq4]
    push_cast
    ring
  · rw [if_neg hv]
    by_cases hv0 : v=0
    · subst v
      rw [if_neg (by omega)]
    · have hv2 : 2≤v := by omega
      rw [if_pos (by omega),if_pos hv2]
end QEC.Coding.TannerLiftedProduct
