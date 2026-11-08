-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.rightDoubleCoverGraph_hasPartiteExpanderMixingBound_of_bilinearBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:46:19.371024+00:00
-- url     : https://prove2.me/submissions/2c9472c1-7f0b-45c9-98df-9a4e0e18cd1a

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightCayleyGraph_isRegular
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rightDoubleCoverGraph_hasPartiteExpanderMixingBound
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
    (label : W → G) (spectral : ℝ)
    (hSymmetric : SmallSetExpansion.IsSymmetric (rightCayleyGraph label))
    (hSpectralNonnegative : 0 ≤ spectral)
    (hSpectral : SmallSetExpansion.HasMeanZeroBilinearBound
      (rightCayleyGraph label) spectral) :
    HasPartiteExpanderMixingBound
      (rightDoubleCoverGraph label) (Fintype.card W) spectral :=
  rightDoubleCoverGraph_hasPartiteExpanderMixingBound
    label (Fintype.card W) spectral hSpectralNonnegative
    (SmallSetExpansion.HasMeanZeroBilinearBound.toExpanderMixingBound
      hSymmetric (rightCayleyGraph_isRegular label)
      hSpectralNonnegative hSpectral)
end QEC.Coding.TannerLiftedProduct
