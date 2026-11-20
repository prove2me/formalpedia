-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:27:52.122011+00:00
-- url     : https://prove2.me/submissions/ccc15291-3d8e-4f9b-97e7-5e0c8176a069

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonDensity_invariant


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq4 : q%4=1)
    (h : SL(2,ℤ)) (τ : ℍ) :
    lpsThetaRankinDensity q hq4 (h • τ)=lpsThetaRankinDensity q hq4 τ := by
  let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
  exact lpsCuspPeterssonDensity_invariant ((4*q)^2) (lpsThetaCuspidalRemainder q hq4) h τ
end QEC.Coding.TannerLiftedProduct
