-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:02:54.31674+00:00
-- url     : https://prove2.me/submissions/a97e0ede-763d-45ba-a3f1-a756422946f0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.Cusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_neg_one_mem

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (ρ : SL(2,ℤ)) :
    (lpsOriginalCuspGroup N ρ).IsRegularAtInfty :=
  Subgroup.isRegularAtInfty_of_neg_one_mem (lpsOriginalCuspGroup_neg_one_mem N ρ)
end QEC.Coding.TannerLiftedProduct
