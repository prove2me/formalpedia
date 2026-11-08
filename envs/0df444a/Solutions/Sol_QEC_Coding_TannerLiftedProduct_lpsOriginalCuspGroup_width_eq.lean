-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_width_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:02:58.671315+00:00
-- url     : https://prove2.me/submissions/513c68f1-b70c-4cbd-9a80-e810efe4c4b6

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
    (lpsOriginalCuspGroup N ρ).widthInfty =
      (lpsOriginalCuspGroup N ρ).strictWidthInfty := by
  rw [Subgroup.widthInfty,
    Subgroup.adjoinNegOne_eq_self_iff.mpr (lpsOriginalCuspGroup_neg_one_mem N ρ)]
end QEC.Coding.TannerLiftedProduct
