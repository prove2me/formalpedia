-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_expanding_of_partiteMixingBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:46:20.951514+00:00
-- url     : https://prove2.me/submissions/4478c0e4-1149-4d63-a541-33409c1b09f1

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_HasPartiteExpanderMixingBound_toSmallSetEdgeExpanding
import Theorems.Thm_QEC_Coding_SmallSetExpansion_HasExpanderMixingBound_toSmallSetEdgeExpanding


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
omit [DecidableEq W]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (radius : Nat) (spectral density : ℝ)
    (hMixing : HasPartiteExpanderMixingBound
      (rightDoubleCoverGraph label) (Fintype.card W) spectral)
    (hDensity : (Fintype.card W : ℝ) * radius ≤
      density * Fintype.card G) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius (spectral + density) :=
  hMixing.toSmallSetEdgeExpanding hDensity
end QEC.Coding.TannerLiftedProduct
