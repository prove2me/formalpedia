-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaEisensteinCorrection_cusp_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:50:48.388017+00:00
-- url     : https://prove2.me/submissions/e6b7bc38-6392-4d6d-aa47-1e090bbb4cc4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisenstein_untwisted_cusp_sum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisenstein_chi4_cusp_sum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisenstein_quadratic_cusp_sum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2DifferenceThetaBasis_cusp_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2ThetaBasis_cusp_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2ThetaBasis_cusp_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisensteinCorrection_slash_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4PrimeE2Twist_cusp_character_tendsto


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq4 : q%4=1)
    (γ : SL(2,ℤ)) :
    Tendsto ((lpsThetaEisensteinCorrection q (by intro h;subst q;norm_num at hq4) : ℍ→ℂ)
      ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (-lpsThetaEisensteinNormalization q *
        (lpsThetaEisensteinTwoCuspFactor γ+lpsChi4EisensteinCuspConstant γ)*
        (lpsThetaEisensteinPrimeCuspFactor q γ+lpsQuadraticEisensteinCuspConstant q γ))) := by
  have hq2 : q≠2 := by intro h;subst q;norm_num at hq4
  have hH := tendsto_finsetSum Finset.univ (fun (a : Fin 5) ha =>
    tendsto_finsetSum Finset.univ (fun (b : Fin 3) hb =>
      (lpsE2DifferenceThetaBasis_cusp_tendsto q a b γ).const_mul
        (lpsThetaEisensteinTwoWeight a*lpsThetaEisensteinPrimeWeight q b)))
  have h4 := tendsto_finsetSum Finset.univ (fun (b : Fin 3) hb =>
    (lpsChi4E2ThetaBasis_cusp_tendsto q hq4 b γ).const_mul (lpsThetaEisensteinChi4Weight q b))
  have hQ := tendsto_finsetSum Finset.univ (fun (a : Fin 5) ha =>
    (lpsQuadraticE2ThetaBasis_cusp_tendsto q hq2 a γ).const_mul (lpsThetaEisensteinQuadraticWeight q a))
  have hK := lpsChi4PrimeE2Twist_cusp_character_tendsto q hq2 γ
  have h := (((hH.add h4).add hQ).sub hK).const_mul (lpsThetaEisensteinNormalization q)
  have hs4 : (∑ b : Fin 3,lpsThetaEisensteinChi4Weight q b*
      (((Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((q^b.val:ℕ):ℂ)^2)*
        lpsChi4EisensteinCuspConstant γ))=
      -lpsThetaEisensteinPrimeCuspFactor q γ*lpsChi4EisensteinCuspConstant γ := by
    have he (b : Fin 3) : lpsThetaEisensteinChi4Weight q b*
        (((Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((q^b.val:ℕ):ℂ)^2)*
          lpsChi4EisensteinCuspConstant γ)=
        (lpsThetaEisensteinChi4Weight q b*
          ((Int.gcd ((q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((q^b.val:ℕ):ℂ)^2))*
          lpsChi4EisensteinCuspConstant γ := by ring
    simp_rw [he]
    rw [←Finset.sum_mul,lpsThetaEisenstein_chi4_cusp_sum]
  have hsQ : (∑ a : Fin 5,lpsThetaEisensteinQuadraticWeight q a*
      (((Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val:ℕ):ℂ)^2)*
        (lpsQuadraticE2Character q ((2^a.val:ℕ):ZMod q)*lpsQuadraticEisensteinCuspConstant q γ)))=
      -lpsThetaEisensteinTwoCuspFactor γ*lpsQuadraticEisensteinCuspConstant q γ := by
    have he (a : Fin 5) : lpsThetaEisensteinQuadraticWeight q a*
        (((Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val:ℕ):ℂ)^2)*
          (lpsQuadraticE2Character q ((2^a.val:ℕ):ZMod q)*lpsQuadraticEisensteinCuspConstant q γ))=
        (lpsThetaEisensteinQuadraticWeight q a*
          ((Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val:ℕ):ℂ)^2)*
            lpsQuadraticE2Character q ((2^a.val:ℕ):ZMod q))*lpsQuadraticEisensteinCuspConstant q γ := by ring
    simp_rw [he]
    rw [←Finset.sum_mul,lpsThetaEisenstein_quadratic_cusp_sum q hq2]
  rw [lpsThetaEisenstein_untwisted_cusp_sum q hq2,hs4,hsQ] at h
  have hc : lpsThetaEisensteinNormalization q *
      ((-lpsThetaEisensteinTwoCuspFactor γ*lpsThetaEisensteinPrimeCuspFactor q γ+
        -lpsThetaEisensteinPrimeCuspFactor q γ*lpsChi4EisensteinCuspConstant γ)+
        -lpsThetaEisensteinTwoCuspFactor γ*lpsQuadraticEisensteinCuspConstant q γ-
        lpsChi4EisensteinCuspConstant γ*lpsQuadraticEisensteinCuspConstant q γ)=
      -lpsThetaEisensteinNormalization q *
        (lpsThetaEisensteinTwoCuspFactor γ+lpsChi4EisensteinCuspConstant γ)*
        (lpsThetaEisensteinPrimeCuspFactor q γ+lpsQuadraticEisensteinCuspConstant q γ) := by ring
  rw [hc,←lpsThetaEisensteinCorrection_slash_eq q hq2 γ] at h
  exact h
end QEC.Coding.TannerLiftedProduct
