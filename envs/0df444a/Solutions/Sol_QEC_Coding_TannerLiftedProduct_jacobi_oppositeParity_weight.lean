-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobi_oppositeParity_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:10:01.579398+00:00
-- url     : https://prove2.me/submissions/49b5bceb-2de2-4e5f-a504-03ffb1212c52

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (s t : ℤ) :
    -(2 * (s + t) + 1) * (2 * (t - s - 1) + 1) =
      (2 * s + 1) ^ 2 - (2 * t) ^ 2 := by
  ring
end QEC.Coding.TannerLiftedProduct
