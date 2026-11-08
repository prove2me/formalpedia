-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.pk22LocalWidth_log_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:16:35.722612+00:00
-- url     : https://prove2.me/submissions/d9443745-45a4-41b6-b70b-f255f9358e4f

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22ParameterBase_le_pow_add_two
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_log_le_exponent_of_le_pow


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (q t : Nat) (hq : 2 ≤ q) :
    Nat.log q (pk22LocalWidth q t) ≤ 4 * t + 8 := by
  apply log_le_exponent_of_le_pow q _ _ (by omega)
  calc
    pk22LocalWidth q t ≤ (q ^ (t + 2)) ^ 4 := by
      exact Nat.pow_le_pow_left (pk22ParameterBase_le_pow_add_two q t hq) 4
    _ = q ^ (4 * t + 8) := by
      rw [← pow_mul]
      congr 1
      omega
end QEC.Coding.TannerLiftedProduct
