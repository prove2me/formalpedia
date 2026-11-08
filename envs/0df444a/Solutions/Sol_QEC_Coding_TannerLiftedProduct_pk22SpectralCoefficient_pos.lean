-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.pk22SpectralCoefficient_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:16:37.370141+00:00
-- url     : https://prove2.me/submissions/8a49ba46-7548-434d-8482-3de701bda833

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22ParameterBase_pos

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q t : Nat) :
    0 < pk22SpectralCoefficient q t := by
  unfold pk22SpectralCoefficient
  exact Nat.mul_pos (by norm_num) (Nat.pow_pos (pk22ParameterBase_pos q t))
end QEC.Coding.TannerLiftedProduct
