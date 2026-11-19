-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinCorrection_slash_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:41:26.725291+00:00
-- url     : https://prove2.me/submissions/4b53a76e-b168-466d-9a39-ca0e0d8bd7b7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4PrimeE2TwistModularForm_apply
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
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) :
    ((lpsThetaEisensteinCorrection q hq2 : ℍ→ℂ) ∣[(2:ℤ)] γ)=
      (fun z => lpsThetaEisensteinNormalization q *
        ((∑ a : Fin 5,∑ b : Fin 3,
          (lpsThetaEisensteinTwoWeight a*lpsThetaEisensteinPrimeWeight q b)*
            (((lpsE2DifferenceThetaBasis q a b : ℍ→ℂ) ∣[(2:ℤ)] γ) z))+
          (∑ b : Fin 3,lpsThetaEisensteinChi4Weight q b*
            (((lpsChi4E2ThetaBasis q b : ℍ→ℂ) ∣[(2:ℤ)] γ) z))+
          (∑ a : Fin 5,lpsThetaEisensteinQuadraticWeight q a*
            (((lpsQuadraticE2ThetaBasis q hq2 a : ℍ→ℂ) ∣[(2:ℤ)] γ) z))-
          ((lpsChi4PrimeE2Twist q ∣[(2:ℤ)] γ) z))) := by
  have hk : (lpsChi4PrimeE2TwistModularForm q hq2 : ℍ→ℂ)=lpsChi4PrimeE2Twist q := by
    funext z
    exact lpsChi4PrimeE2TwistModularForm_apply q hq2 z
  simp only [lpsThetaEisensteinCorrection,FunLike.coe_smul,FunLike.coe_neg,FunLike.coe_add,
    FunLike.coe_sum,sub_eq_add_neg,SlashAction.add_slash,SlashAction.neg_slash,
    SlashAction.sum_slash,ModularForm.SL_smul_slash,hk]
  funext z
  simp only [Pi.smul_apply,Pi.add_apply,Pi.neg_apply,Finset.sum_apply,smul_eq_mul]
end QEC.Coding.TannerLiftedProduct
