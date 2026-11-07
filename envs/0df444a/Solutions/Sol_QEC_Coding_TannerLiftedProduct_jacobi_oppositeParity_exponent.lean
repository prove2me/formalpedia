-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobi_oppositeParity_exponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:09:53.896215+00:00
-- url     : https://prove2.me/submissions/72f39473-8cb4-4941-b4a7-839b966fe92e

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (s t : ℤ) :
    (s + t) ^ 2 + (s + t) + (t - s - 1) ^ 2 + (t - s - 1) =
      2 * (s ^ 2 + s + t ^ 2) := by
  ring
end QEC.Coding.TannerLiftedProduct
