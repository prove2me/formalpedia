-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_expanding_of_bilinearBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:46:30.418137+00:00
-- url     : https://prove2.me/submissions/2bd54cd3-b705-48b5-8c11-a7e212106e8c

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverGraph_isSymmetric
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverGraph_isRegular
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_HasPartiteExpanderMixingBound_toSmallSetEdgeExpanding
import Theorems.Thm_QEC_Coding_SmallSetExpansion_HasExpanderMixingBound_toSmallSetEdgeExpanding
import Theorems.Thm_QEC_Coding_SmallSetExpansion_HasMeanZeroBilinearBound_toExpanderMixingBound


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
    (hSpectralNonnegative : 0 ≤ spectral)
    (hSpectral : SmallSetExpansion.HasMeanZeroBilinearBound
      (rightDoubleCoverGraph label) spectral)
    (hDensity : (Fintype.card W : ℝ) * radius ≤
      density * Fintype.card (Fin 2 × G)) :
    SmallSetExpansion.IsSmallSetEdgeExpanding
      (rightDoubleCoverGraph label) radius (spectral + density) := by
  exact
    (SmallSetExpansion.HasMeanZeroBilinearBound.toExpanderMixingBound
      (rightDoubleCoverGraph_isSymmetric label)
      (rightDoubleCoverGraph_isRegular label)
      hSpectralNonnegative hSpectral).toSmallSetEdgeExpanding hDensity
end QEC.Coding.TannerLiftedProduct
