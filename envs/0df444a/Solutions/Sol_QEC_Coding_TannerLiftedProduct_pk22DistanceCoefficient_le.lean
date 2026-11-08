-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.pk22DistanceCoefficient_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:12:09.402404+00:00
-- url     : https://prove2.me/submissions/07b898a7-8f58-4708-8f7e-b0fa448699fa

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22ParameterBase_le_three_mul_pow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (q t : Nat) (hq : 2 ≤ q) :
    pk22DistanceCoefficient q t ≤ 4608 * q ^ (2 * t) := by
  have hBase := pk22ParameterBase_le_three_mul_pow q t (by omega)
  unfold pk22DistanceCoefficient pk22SpectralCoefficient
  calc
    32 * (16 * pk22ParameterBase q t ^ 2) =
        512 * pk22ParameterBase q t ^ 2 := by ring
    _ ≤ 512 * (3 * q ^ t) ^ 2 := by gcongr
    _ = 4608 * q ^ (2 * t) := by rw [mul_pow, ← pow_mul]; ring
end QEC.Coding.TannerLiftedProduct
