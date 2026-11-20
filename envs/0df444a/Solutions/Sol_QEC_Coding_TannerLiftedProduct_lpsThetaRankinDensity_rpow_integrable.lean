-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_rpow_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:29:21.718182+00:00
-- url     : https://prove2.me/submissions/5fb5ff97-0fe3-4cbb-9e21-95688fce1507

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_rpow_integrable


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) (s : ℝ) :
    IntegrableOn (fun τ : ℍ => lpsThetaRankinDensity q hq4 τ*τ.im^s) ModularGroup.fd := by
  let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
  exact lpsCuspPeterssonDensity_rpow_integrable ((4*q)^2) (lpsThetaCuspidalRemainder q hq4) _
end QEC.Coding.TannerLiftedProduct
