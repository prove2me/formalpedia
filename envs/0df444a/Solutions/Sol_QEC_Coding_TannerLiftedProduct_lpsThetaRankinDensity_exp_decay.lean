-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_exp_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:27:55.417197+00:00
-- url     : https://prove2.me/submissions/4884e610-20a2-41b0-88cb-c02f5c0e239f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_exp_decay


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    ∃a>0,lpsThetaRankinDensity q hq4=O[atImInfty] (fun τ => Real.exp (-a*τ.im)) := by
  let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
  exact lpsCuspPeterssonDensity_exp_decay ((4*q)^2) (lpsThetaCuspidalRemainder q hq4)
end QEC.Coding.TannerLiftedProduct
