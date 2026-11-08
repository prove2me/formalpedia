-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsScaleQuaternion_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:37:59.670264+00:00
-- url     : https://prove2.me/submissions/a5568759-2378-4f17-b249-a908d57336c9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionExactDivision

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {s : ℤ} (hs : s ≠ 0) :
    Function.Injective (lpsScaleQuaternion s) := by
  intro t u h
  apply LPSQuaternion.ext
  · exact mul_left_cancel₀ hs (congrArg LPSQuaternion.a h)
  · exact mul_left_cancel₀ hs (congrArg LPSQuaternion.b h)
  · exact mul_left_cancel₀ hs (congrArg LPSQuaternion.c h)
  · exact mul_left_cancel₀ hs (congrArg LPSQuaternion.d h)
end QEC.Coding.TannerLiftedProduct
