-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2ThetaBasis_cusp_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:41:23.443418+00:00
-- url     : https://prove2.me/submissions/161c962f-ba73-4a63-a555-0e095641d545

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Dilate_cusp_coprime_tendsto


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (a : Fin 5) (γ : SL(2,ℤ)) :
    Tendsto ((lpsQuadraticE2ThetaBasis q hq2 a : ℍ→ℂ) ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (((Int.gcd ((2^a.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val:ℕ):ℂ)^2)*
        (lpsQuadraticE2Character q ((2^a.val:ℕ):ZMod q)*lpsQuadraticEisensteinCuspConstant q γ))) := by
  have hc := ((Fact.out : q.Prime).odd_of_ne_two hq2).coprime_two_left.pow_left a.val
  exact lpsQuadraticE2Dilate_cusp_coprime_tendsto q (2^a.val) hq2 (pow_pos (by decide) _) hc γ
end QEC.Coding.TannerLiftedProduct
