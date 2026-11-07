-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:09:50.260114+00:00
-- url     : https://prove2.me/submissions/c3546cb5-d5c5-4a8a-9670-9d7949966d22

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (s t : ℤ) :
    jacobiParityReindex (Sum.inl (s, t)) = (s + t, s - t) := by
  rfl
end QEC.Coding.TannerLiftedProduct
