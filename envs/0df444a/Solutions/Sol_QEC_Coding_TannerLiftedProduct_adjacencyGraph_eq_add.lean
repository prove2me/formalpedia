-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.adjacencyGraph_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:04:43.115902+00:00
-- url     : https://prove2.me/submissions/325eb66d-1de1-4c56-97f2-fe76a1e45512

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_SmallSetExpansion_IsSmallSetEdgeExpanding_add
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [Fintype G] [DecidableEq W]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (label : W → G) :
    adjacencyGraph label =
      SmallSetExpansion.add (horizontalGraph label) (verticalGraph label) := by
  rfl
end QEC.Coding.TannerLiftedProduct
