-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.pk22_rateCoefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:22:39.966704+00:00
-- url     : https://prove2.me/submissions/21870653-ea42-4dae-ad12-1fd8e06d6687

import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalParameterSelection
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pow_le_pk22ParameterBase
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_pk22RowCoefficient_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (q t : Nat) (hq : 2 ≤ q) (rate : ℝ) (hRate : rate < 1)
    (hLarge : (4 * 124421 : ℝ) <
      (1 - rate) * ((q ^ t : Nat) : ℝ)) :
    2 * ((pk22RowCoefficient q t : ℝ) + pk22RowCoefficient q t) *
        pk22LocalWidth q t ≤
      (1 - rate) *
        ((pk22LocalWidth q t : ℝ) ^ 2 +
          4 * (pk22RowCoefficient q t : ℝ) * pk22RowCoefficient q t) := by
  have hRows := pk22RowCoefficient_le q t hq
  have hWidthLower : q ^ (4 * t) ≤ pk22LocalWidth q t := by
    unfold pk22LocalWidth
    calc
      q ^ (4 * t) = (q ^ t) ^ 4 := by
        rw [show 4 * t = t * 4 by omega, pow_mul]
      _ ≤ pk22ParameterBase q t ^ 4 :=
        Nat.pow_le_pow_left (pow_le_pk22ParameterBase q t) 4
  have hPowPositiveReal : (0 : ℝ) < ((q ^ (3 * t) : Nat) : ℝ) := by
    positivity
  have hRowsRate :
      4 * (pk22RowCoefficient q t : ℝ) <
        (1 - rate) * (pk22LocalWidth q t : ℝ) := by
    calc
      4 * (pk22RowCoefficient q t : ℝ) ≤
          ((4 * (124421 * q ^ (3 * t)) : Nat) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_left 4 hRows
      _ = (4 * 124421 : ℝ) * ((q ^ (3 * t) : Nat) : ℝ) := by
        push_cast
        ring
      _ < ((1 - rate) * ((q ^ t : Nat) : ℝ)) *
          ((q ^ (3 * t) : Nat) : ℝ) :=
        mul_lt_mul_of_pos_right hLarge hPowPositiveReal
      _ = (1 - rate) * ((q ^ (4 * t) : Nat) : ℝ) := by
        push_cast
        rw [show 4 * t = t + 3 * t by omega, pow_add]
        ring
      _ ≤ (1 - rate) * (pk22LocalWidth q t : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hRate.le)
        exact_mod_cast hWidthLower
  have hWidthNonnegative : (0 : ℝ) ≤ pk22LocalWidth q t := by positivity
  have hRowsNonnegative : (0 : ℝ) ≤ pk22RowCoefficient q t := by positivity
  nlinarith [sq_nonneg (pk22LocalWidth q t : ℝ),
    sq_nonneg (pk22RowCoefficient q t : ℝ)]
end QEC.Coding.TannerLiftedProduct
