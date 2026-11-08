-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGluedChartMap_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:52:40.82512+00:00
-- url     : https://prove2.me/submissions/71619495-bfd1-42d9-889b-8317e3816710

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
    (N : ℕ) (hN : 0<N) (x : lpsOriginalComplexNormalGluedScheme N hN) :
    ∃ (b : Bool) (y : lpsOriginalComplexNormalSchemeChart N hN b),
      lpsOriginalComplexNormalGluedChartMap N hN b y=x :=
  (lpsOriginalComplexNormalSchemeGlueData N hN).ι_jointly_surjective x
end QEC.Coding.TannerLiftedProduct
