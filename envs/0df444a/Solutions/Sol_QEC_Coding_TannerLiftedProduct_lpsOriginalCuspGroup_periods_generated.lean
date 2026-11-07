-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_periods_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:22:43.805256+00:00
-- url     : https://prove2.me/submissions/ea35cef0-bf45-4dba-a16d-619a83511010

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.Cusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (ρ : SL(2,ℤ)) :
    (lpsOriginalCuspGroup N ρ).strictPeriods =
      AddSubgroup.zmultiples (lpsOriginalCuspGroup N ρ).strictWidthInfty :=
  Subgroup.strictPeriods_eq_zmultiples_strictWidthInfty
end QEC.Coding.TannerLiftedProduct
