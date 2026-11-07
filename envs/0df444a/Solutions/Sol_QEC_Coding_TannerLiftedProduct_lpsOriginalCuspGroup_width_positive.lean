-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_width_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:27:13.301124+00:00
-- url     : https://prove2.me/submissions/9efbb291-4785-4680-9ee1-9b9ec7e32e45

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.Cusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_integerPeriod

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (ρ : SL(2,ℤ)) :
    0 < (lpsOriginalCuspGroup N ρ).strictWidthInfty := by
  apply Subgroup.strictWidthInfty_pos_iff.mpr
  exact Subgroup.isCusp_of_mem_strictPeriods
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
    (lpsOriginalCuspGroup_integerPeriod N ρ)
end QEC.Coding.TannerLiftedProduct
