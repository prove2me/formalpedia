-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.pk22_rankCoefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:16:39.082741+00:00
-- url     : https://prove2.me/submissions/dfc9cb91-5bf0-4274-9e1c-69738f8736a3

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q t : Nat) :
    36 * 1 * pk22FaceCoefficient q t ≤
      5 * (pk22DistanceCoefficient q t) ^ 2 := by
  unfold pk22FaceCoefficient pk22DistanceCoefficient
  calc
    36 * 1 * (112 * pk22SpectralCoefficient q t ^ 2) =
        4032 * pk22SpectralCoefficient q t ^ 2 := by ring
    _ ≤ 5120 * pk22SpectralCoefficient q t ^ 2 :=
      Nat.mul_le_mul_right _ (by norm_num)
    _ = 5 * (32 * pk22SpectralCoefficient q t) ^ 2 := by ring
end QEC.Coding.TannerLiftedProduct
