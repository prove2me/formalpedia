-- Prove2me | solution 1 for QEC.Locality.profileDivisionPotential_le_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:29:58.497032+00:00
-- url     : https://prove2.me/submissions/fdac5c1c-60a0-46e5-8d42-3ac57edb23c8

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_DivisionPotential
import Theorems.Thm_QEC_Locality_profileDivisionPotentialCoefficient_nonneg
import Theorems.Thm_QEC_Locality_profileDivisionPotential_le_linear

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
namespace QEC.Locality
theorem _root_.solution
    {beta exponent : ℝ} {r parent : Nat}
    (hbeta : 0 ≤ beta) (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 1 ≤ r) :
    profileDivisionPotential beta exponent r parent ≤
      (profileDivisionPotentialCoefficient beta exponent /
        (1 / 4 : ℝ) ^ (1 - exponent)) * parent := by
  have hrPos : 0 < r := Nat.zero_lt_of_lt hr
  have hrReal : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrpow : (r : ℝ) ^ (exponent - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hrReal (by linarith)
  have hcoefficient : 0 ≤ profileDivisionPotentialCoefficient beta exponent :=
    profileDivisionPotentialCoefficient_nonneg hbeta hexponent
  have hquarterPow : 0 < (1 / 4 : ℝ) ^ (1 - exponent) :=
    Real.rpow_pos_of_pos (by norm_num) _
  calc
    profileDivisionPotential beta exponent r parent ≤
        profileDivisionPotentialCoefficient beta exponent *
          ((parent : ℝ) * (r : ℝ) ^ (exponent - 1) /
            (1 / 4 : ℝ) ^ (1 - exponent)) :=
      profileDivisionPotential_le_linear hbeta hexponent hrPos
    _ ≤ profileDivisionPotentialCoefficient beta exponent *
          ((parent : ℝ) * 1 / (1 / 4 : ℝ) ^ (1 - exponent)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrpow (Nat.cast_nonneg parent)) hquarterPow.le)
        hcoefficient
    _ = (profileDivisionPotentialCoefficient beta exponent /
          (1 / 4 : ℝ) ^ (1 - exponent)) * parent := by ring
end QEC.Locality
