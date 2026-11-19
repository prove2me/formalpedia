-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2DifferenceThetaBasis_cusp_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:41:19.75554+00:00
-- url     : https://prove2.me/submissions/8091f47e-b9f4-4491-b4d7-0c50a542e651

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime]
    (a : Fin 5) (b : Fin 3) (γ : SL(2,ℤ)) :
    Tendsto ((lpsE2DifferenceThetaBasis q a b : ℍ→ℂ) ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 (1-(Int.gcd ((2^a.val*q^b.val:ℕ):ℤ) (γ 1 0):ℂ)^2/((2^a.val*q^b.val:ℕ):ℂ))) := by
  have h := lpsE2Difference_cusp_tendsto (2^a.val*q^b.val)
    (mul_pos (pow_pos (by decide) _) (pow_pos (Fact.out : q.Prime).pos _)) γ
  rw [lpsEisensteinDilation_column_gcd] at h
  exact h
end QEC.Coding.TannerLiftedProduct
