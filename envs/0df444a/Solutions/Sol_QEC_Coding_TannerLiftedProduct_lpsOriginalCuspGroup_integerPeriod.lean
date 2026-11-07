-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_integerPeriod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:25:40.850824+00:00
-- url     : https://prove2.me/submissions/7c773dc2-ddb5-4be9-a22f-e9ff6b6922a3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.Cusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Translate_integerPeriod


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (ρ : SL(2,ℤ)) :
    (N:ℝ) ∈ (lpsOriginalCuspGroup N ρ).strictPeriods :=
  lpsGamma0Translate_integerPeriod N ρ
end QEC.Coding.TannerLiftedProduct
