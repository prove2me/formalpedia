-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.pk22RowCoefficient_twice_le_localWidth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:22:36.80211+00:00
-- url     : https://prove2.me/submissions/f16b46a7-f9ab-4556-826e-6e328537218a

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pow_le_pk22ParameterBase
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22RowCoefficient_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (q t : Nat) (hq : 2 ≤ q)
    (hLarge : 2 * 124421 ≤ q ^ t) :
    2 * pk22RowCoefficient q t ≤ pk22LocalWidth q t := by
  have hRows := pk22RowCoefficient_le q t hq
  have hPowPositive : 0 < q ^ (3 * t) := Nat.pow_pos (by omega)
  have hWidthLower : q ^ (4 * t) ≤ pk22LocalWidth q t := by
    unfold pk22LocalWidth
    calc
      q ^ (4 * t) = (q ^ t) ^ 4 := by
        rw [show 4 * t = t * 4 by omega, pow_mul]
      _ ≤ pk22ParameterBase q t ^ 4 :=
        Nat.pow_le_pow_left (pow_le_pk22ParameterBase q t) 4
  calc
    2 * pk22RowCoefficient q t ≤
        2 * (124421 * q ^ (3 * t)) := Nat.mul_le_mul_left 2 hRows
    _ = (2 * 124421) * q ^ (3 * t) := by ring
    _ ≤ q ^ t * q ^ (3 * t) := Nat.mul_le_mul_right _ hLarge
    _ = q ^ (4 * t) := by rw [← pow_add]; congr 1; omega
    _ ≤ pk22LocalWidth q t := hWidthLower
end QEC.Coding.TannerLiftedProduct
