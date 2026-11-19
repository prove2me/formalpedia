-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaEisenstein_quadratic_cusp_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:48:54.760628+00:00
-- url     : https://prove2.me/submissions/12480abb-5025-41d2-abcf-2d2cc2a00cf5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaEisensteinQuadraticWeight_scaled

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) :
    (∑ a : Fin 5,lpsThetaEisensteinQuadraticWeight q a*
      ((Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val:ℕ):ℂ)^2)*
        lpsQuadraticE2Character q ((2^a.val:ℕ):ZMod q))=
      -lpsThetaEisensteinTwoCuspFactor γ := by
  have he (a : Fin 5) : lpsThetaEisensteinQuadraticWeight q a*
      ((Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val:ℕ):ℂ)^2)*
        lpsQuadraticE2Character q ((2^a.val:ℕ):ZMod q)=
      -(lpsThetaEisensteinTwoWeight a*(Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/
        ((2^a.val:ℕ):ℂ)) := by
    calc
      _=(lpsThetaEisensteinQuadraticWeight q a*lpsQuadraticE2Character q ((2^a.val:ℕ):ZMod q)/
        ((2^a.val:ℕ):ℂ)^2)*(Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2 := by ring
      _=_ := by rw [lpsThetaEisensteinQuadraticWeight_scaled q hq2];ring
  simp_rw [he]
  rw [Finset.sum_neg_distrib]
  rfl
end QEC.Coding.TannerLiftedProduct
