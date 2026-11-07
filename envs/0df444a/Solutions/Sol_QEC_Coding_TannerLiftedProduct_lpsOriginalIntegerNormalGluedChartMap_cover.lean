-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedChartMap_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:56:37.708769+00:00
-- url     : https://prove2.me/submissions/433deb61-89ed-4206-a516-bbeb8b15db11

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
    (N : ℕ) (hN : 0<N) (x : lpsOriginalIntegerNormalGluedScheme N hN) :
    ∃ (b : Bool) (y : lpsOriginalIntegerNormalSchemeChart N hN b),
      lpsOriginalIntegerNormalGluedChartMap N hN b y=x :=
  (lpsOriginalIntegerNormalSchemeGlueData N hN).ι_jointly_surjective x
end QEC.Coding.TannerLiftedProduct
