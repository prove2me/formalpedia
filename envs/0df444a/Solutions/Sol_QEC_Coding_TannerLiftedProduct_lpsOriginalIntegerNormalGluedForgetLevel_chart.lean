-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedForgetLevel_chart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:14:09.381675+00:00
-- url     : https://prove2.me/submissions/1280d170-4397-4763-85df-167c23c71c62

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelMorphism

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (h4N : 4 ∣ N)
    (hN : 0 < N) (hM : 0 < M) (b : Bool) :
    lpsOriginalIntegerNormalGluedChartMap M hM b ≫
      lpsOriginalIntegerNormalGluedForgetLevel N M hNM h4N hN hM =
    lpsOriginalIntegerNormalSchemeLevelChartMap N M hNM h4N hN hM b ≫
      lpsOriginalIntegerNormalGluedChartMap N hN b :=
  Multicoequalizer.π_desc _ _ _ _ _
end QEC.Coding.TannerLiftedProduct
