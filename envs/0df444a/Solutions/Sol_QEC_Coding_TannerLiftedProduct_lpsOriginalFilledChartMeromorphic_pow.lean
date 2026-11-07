-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledChartMeromorphic_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:32:07.312715+00:00
-- url     : https://prove2.me/submissions/0f83044c-3517-4a33-bc12-bb3a4061f12d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicRestriction
import Mathlib.Analysis.Analytic.Polynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    {F : LPSOriginalFilledCurve N → ℂ}
    (hF : lpsOriginalFilledChartMeromorphic N hN F) (m : ℕ) :
    lpsOriginalFilledChartMeromorphic N hN (F^m) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  intro x z hz
  exact (hF x z hz).pow m
end QEC.Coding.TannerLiftedProduct
