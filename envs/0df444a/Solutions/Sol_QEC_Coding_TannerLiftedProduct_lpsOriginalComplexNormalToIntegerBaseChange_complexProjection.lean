-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalToIntegerBaseChange_complexProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:53:18.394086+00:00
-- url     : https://prove2.me/submissions/ba5a5639-12ba-4493-92ae-7d4085ed4e33

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLaurentNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_NormalizationBaseChange
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
open QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open scoped TensorProduct
noncomputable section
local notation "JC" => FractionRing (Polynomial ℂ)
attribute [local instance] QEC.Coding.TannerLiftedProduct.complexGluingDictionary001
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 0<N) :
    lpsOriginalComplexNormalToIntegerBaseChange N hN ≫ pullback.fst _ _ =
      lpsOriginalComplexNormalGluedToSpecC N hN :=
  pullback.lift_fst _ _ _
end QEC.Coding.TannerLiftedProduct
