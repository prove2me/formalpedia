-- Prove2me | solution 1 for WeierstrassCurve.laurentFrame_wUnitFactor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3fbc71b8-7c34-5671-85a1-1a8aee3b369a

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_laurentFrame_wUnitFactor

set_option autoImplicit false

open FormalGroup

theorem solution
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    (-(HahnSeries.single (-3 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor)) ^ 2 + HahnSeries.C W.a₁ * (HahnSeries.single (-2 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor) * (-(HahnSeries.single (-3 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor)) + HahnSeries.C W.a₃ * (-(HahnSeries.single (-3 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor))
        = (HahnSeries.single (-2 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor) ^ 3 + HahnSeries.C W.a₂ * (HahnSeries.single (-2 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor) ^ 2 + HahnSeries.C W.a₄ * (HahnSeries.single (-2 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor) + HahnSeries.C W.a₆ ∧
    (HahnSeries.single (-2 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor).coeff (-2) = 1 ∧ (∀ n < -2, (HahnSeries.single (-2 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor).coeff n = 0) ∧
    (-(HahnSeries.single (-3 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor)).coeff (-3) = -1 ∧ (∀ n < -3, (-(HahnSeries.single (-3 : ℤ) (1 : R) * HahnSeries.ofPowerSeries ℤ R W.wUnitFactor)).coeff n = 0) := by

  set U : LaurentSeries R := HahnSeries.ofPowerSeries ℤ R W.wUnitFactor with hU
  set S : LaurentSeries R := HahnSeries.single (-1 : ℤ) (1 : R) with hS
  set Z : LaurentSeries R := HahnSeries.single (1 : ℤ) (1 : R) with hZ
  have hS2 : HahnSeries.single (-2 : ℤ) (1 : R) = S ^ 2 := by
    rw [hS, HahnSeries.single_pow]; norm_num
  have hS3 : HahnSeries.single (-3 : ℤ) (1 : R) = S ^ 3 := by
    rw [hS, HahnSeries.single_pow]; norm_num
  have hZS : Z * S = 1 := by rw [hZ, hS, HahnSeries.single_mul_single]; norm_num

  have hu : W.wUnitFactor = 1 - (PowerSeries.C W.a₁ * PowerSeries.X + PowerSeries.C W.a₂ * PowerSeries.X ^ 2
      + PowerSeries.C W.a₃ * W.formalW + PowerSeries.C W.a₄ * (PowerSeries.X * W.formalW)
      + PowerSeries.C W.a₆ * W.formalW ^ 2) := rfl
  have hwu := W.formalW_mul_wUnitFactor
  have star : W.wUnitFactor ^ 2 - PowerSeries.C W.a₁ * PowerSeries.X * W.wUnitFactor ^ 2
      - PowerSeries.C W.a₃ * PowerSeries.X ^ 3 * W.wUnitFactor
      = W.wUnitFactor ^ 3 + PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * W.wUnitFactor ^ 2
        + PowerSeries.C W.a₄ * PowerSeries.X ^ 4 * W.wUnitFactor + PowerSeries.C W.a₆ * PowerSeries.X ^ 6 := by
    linear_combination (-(W.wUnitFactor ^ 2)) * hu
      + (PowerSeries.C W.a₃ * W.wUnitFactor + PowerSeries.C W.a₄ * PowerSeries.X * W.wUnitFactor
          + PowerSeries.C W.a₆ * (W.formalW * W.wUnitFactor + PowerSeries.X ^ 3)) * hwu

  have starL := congrArg (HahnSeries.ofPowerSeries ℤ R) star
  simp only [map_sub, map_add, map_mul, map_pow, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X] at starL
  rw [← hU, ← hZ] at starL
  have hZu : IsUnit (Z ^ 6) := (IsUnit.of_mul_eq_one S hZS).pow 6
  have h6 : Z ^ 6 * S ^ 6 = 1 := by rw [← mul_pow, hZS, one_pow]
  have h5 : Z ^ 6 * S ^ 5 = Z := by rw [show Z ^ 6 * S ^ 5 = Z * (Z * S) ^ 5 by ring, hZS, one_pow, mul_one]
  have h4 : Z ^ 6 * S ^ 4 = Z ^ 2 := by rw [show Z ^ 6 * S ^ 4 = Z ^ 2 * (Z * S) ^ 4 by ring, hZS, one_pow, mul_one]
  have h3 : Z ^ 6 * S ^ 3 = Z ^ 3 := by rw [show Z ^ 6 * S ^ 3 = Z ^ 3 * (Z * S) ^ 3 by ring, hZS, one_pow, mul_one]
  have h2 : Z ^ 6 * S ^ 2 = Z ^ 4 := by rw [show Z ^ 6 * S ^ 2 = Z ^ 4 * (Z * S) ^ 2 by ring, hZS, one_pow, mul_one]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hS2, hS3]
    refine hZu.mul_left_cancel ?_
    linear_combination starL + (U ^ 2 - U ^ 3) * h6 - HahnSeries.C W.a₁ * U ^ 2 * h5
      - HahnSeries.C W.a₃ * U * h3 - HahnSeries.C W.a₂ * U ^ 2 * h4 - HahnSeries.C W.a₄ * U * h2
  · rw [HahnSeries.coeff_single_mul, one_mul, hU, show ((-2 : ℤ) - -2) = ((0 : ℕ) : ℤ) by norm_num,
      HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_eq_constantCoeff, W.constantCoeff_wUnitFactor]
  · intro n hn
    rw [HahnSeries.coeff_single_mul, one_mul, hU]
    show ((W.wUnitFactor : PowerSeries R) : LaurentSeries R).coeff (n - -2) = 0
    rw [PowerSeries.coeff_coe, if_pos (by omega)]
  · rw [HahnSeries.coeff_neg, HahnSeries.coeff_single_mul, one_mul, hU, show ((-3 : ℤ) - -3) = ((0 : ℕ) : ℤ) by norm_num,
      HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_eq_constantCoeff, W.constantCoeff_wUnitFactor]
  · intro n hn
    rw [HahnSeries.coeff_neg, HahnSeries.coeff_single_mul, one_mul, hU, neg_eq_zero]
    show ((W.wUnitFactor : PowerSeries R) : LaurentSeries R).coeff (n - -3) = 0
    rw [PowerSeries.coeff_coe, if_pos (by omega)]

end S_WeierstrassCurve_laurentFrame_wUnitFactor
end P2MW
export P2MW.S_WeierstrassCurve_laurentFrame_wUnitFactor (solution)
