-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobi_sameParity_exponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:09:37.802707+00:00
-- url     : https://prove2.me/submissions/934788cb-904c-4cb1-b874-d0d51800b93a

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (s t : ℤ) :
    (s + t) ^ 2 + (s + t) + (s - t) ^ 2 + (s - t) =
      2 * (s ^ 2 + s + t ^ 2) := by
  ring
end QEC.Coding.TannerLiftedProduct
