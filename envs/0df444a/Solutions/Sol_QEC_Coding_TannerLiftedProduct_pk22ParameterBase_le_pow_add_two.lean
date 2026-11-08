-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.pk22ParameterBase_le_pow_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:12:07.510198+00:00
-- url     : https://prove2.me/submissions/7e6b0f21-5493-43bb-be38-6e876ccc085d

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22ParameterBase_le_three_mul_pow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (q t : Nat) (hq : 2 ≤ q) :
    pk22ParameterBase q t ≤ q ^ (t + 2) := by
  have hqPositive : 0 < q := by omega
  calc
    pk22ParameterBase q t ≤ 3 * q ^ t :=
      pk22ParameterBase_le_three_mul_pow q t hqPositive
    _ ≤ q ^ 2 * q ^ t := by
      gcongr
      nlinarith
    _ = q ^ (t + 2) := by rw [pow_add]; ring
end QEC.Coding.TannerLiftedProduct
