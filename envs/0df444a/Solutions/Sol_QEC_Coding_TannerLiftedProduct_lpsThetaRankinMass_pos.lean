-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaRankinMass_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:05:27.853203+00:00
-- url     : https://prove2.me/submissions/cb6966ec-a3b2-49e3-8610-7e8394c137af

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaPeterssonPositive
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspidalRemainder_ne_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonMass_pos_iff


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    0<lpsThetaRankinMass q hq4 := by
  let : NeZero ((4*q)^2) := ⟨by have := (Fact.out : q.Prime).pos;positivity⟩
  exact (lpsCuspPeterssonMass_pos_iff ((4*q)^2) (lpsThetaCuspidalRemainder q hq4)).mpr
    (lpsThetaCuspidalRemainder_ne_zero q hq4)
end QEC.Coding.TannerLiftedProduct
