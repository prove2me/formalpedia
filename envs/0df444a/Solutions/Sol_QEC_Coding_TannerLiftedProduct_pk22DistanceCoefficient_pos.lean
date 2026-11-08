-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.pk22DistanceCoefficient_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:28:24.39309+00:00
-- url     : https://prove2.me/submissions/9b7e32dd-f8bd-404a-a47e-a22f9bea4530

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22ParameterBase_pos

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q t : Nat) :
    0 < pk22DistanceCoefficient q t := by
  unfold pk22DistanceCoefficient pk22SpectralCoefficient
  exact Nat.mul_pos (by norm_num)
    (Nat.mul_pos (by norm_num) (Nat.pow_pos (pk22ParameterBase_pos q t)))
end QEC.Coding.TannerLiftedProduct
