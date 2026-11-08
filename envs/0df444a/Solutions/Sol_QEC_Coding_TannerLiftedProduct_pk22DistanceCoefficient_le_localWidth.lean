-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.pk22DistanceCoefficient_le_localWidth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:12:11.263318+00:00
-- url     : https://prove2.me/submissions/3eaf8d07-ac2f-495b-b44c-d1e07c838c0e

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pow_le_pk22ParameterBase

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (q t : Nat) (_hq : 2 ≤ q) (hLarge : 23 ≤ q ^ t) :
    pk22DistanceCoefficient q t ≤ pk22LocalWidth q t := by
  have hBaseLarge : 23 ≤ pk22ParameterBase q t :=
    hLarge.trans (pow_le_pk22ParameterBase q t)
  unfold pk22DistanceCoefficient pk22SpectralCoefficient pk22LocalWidth
  have hSquare : 512 ≤ pk22ParameterBase q t ^ 2 := by nlinarith
  calc
    32 * (16 * pk22ParameterBase q t ^ 2) =
        512 * pk22ParameterBase q t ^ 2 := by ring
    _ ≤ pk22ParameterBase q t ^ 2 * pk22ParameterBase q t ^ 2 :=
      Nat.mul_le_mul_right _ hSquare
    _ = pk22ParameterBase q t ^ 4 := by ring
end QEC.Coding.TannerLiftedProduct
