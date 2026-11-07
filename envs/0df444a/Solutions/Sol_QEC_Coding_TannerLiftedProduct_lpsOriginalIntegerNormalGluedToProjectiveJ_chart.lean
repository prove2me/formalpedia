-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedToProjectiveJ_chart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:54:45.969889+00:00
-- url     : https://prove2.me/submissions/dabc5a1e-e8d5-4ca1-8b5c-c7aa9e9589e3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0<N) (b : Bool) :
    lpsOriginalIntegerNormalGluedChartMap N hN b ≫
      lpsOriginalIntegerNormalGluedToProjectiveJ N hN =
    lpsOriginalIntegerNormalChartToProjectiveJ N hN b :=
  Multicoequalizer.π_desc _ _ _ _ _
end QEC.Coding.TannerLiftedProduct
