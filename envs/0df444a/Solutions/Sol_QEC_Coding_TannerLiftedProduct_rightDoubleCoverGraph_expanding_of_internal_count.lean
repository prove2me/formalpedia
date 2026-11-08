-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_expanding_of_internal_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:46:41.982657+00:00
-- url     : https://prove2.me/submissions/919c1844-1325-4ffe-843f-c0e4f16b888b

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverGraph_isSymmetric
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverGraph_isRegular
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_of_internal_count


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [DecidableEq W]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (radius : Nat) (internalConstant : ℝ)
    (hInternalNonnegative : 0 ≤ internalConstant)
    (hInternal : ∀ U : Finset (Fin 2 × G), U.card ≤ 2 * radius →
      (SmallSetExpansion.crossCount
        (rightDoubleCoverGraph label) U U : ℝ) ≤
          internalConstant * U.card) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius
      (Real.sqrt (2 * internalConstant * Fintype.card W)) := by
  exact SmallSetExpansion.IsSmallSetEdgeExpanding.of_internal_count
    (rightDoubleCoverGraph label) radius (Fintype.card W) internalConstant
    (rightDoubleCoverGraph_isSymmetric label)
    (rightDoubleCoverGraph_isRegular label)
    hInternalNonnegative hInternal
end QEC.Coding.TannerLiftedProduct
