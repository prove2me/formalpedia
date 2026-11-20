-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_remainder_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:28:41.991307+00:00
-- url     : https://prove2.me/submissions/7c9f296b-9e1e-4760-be9a-dda72305f449

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_individual_le


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) (τ : ℍ) :
    ‖lpsStandardTheta q τ-lpsThetaEisensteinCorrection q
      (by intro h;subst q;norm_num at hq4) τ‖^2*τ.im^2≤lpsThetaRankinDensity q hq4 τ := by
  let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
  exact lpsCuspPeterssonDensity_individual_le ((4*q)^2) (lpsThetaCuspidalRemainder q hq4) _
end QEC.Coding.TannerLiftedProduct
