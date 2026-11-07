-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:09:51.48322+00:00
-- url     : https://prove2.me/submissions/d76526c9-19b0-4f08-95cf-151c55161429

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (s t : ℤ) :
    jacobiParityReindex (Sum.inr (s, t)) = (s + t, t - s - 1) := by
  rfl
end QEC.Coding.TannerLiftedProduct
