-- Prove2me | solution 1 for QEC.Locality.profileDivisionPotential_le_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:41:41.472205+00:00
-- url     : https://prove2.me/submissions/5e032686-35ed-4289-9e14-08848bfaa11e

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
import Definitions.Def_QEC_Locality_SeparatorProfile_Quantitative
import Definitions.Def_QEC_Locality_SeparatorProfile_DivisionPotential
import Theorems.Thm_QEC_Locality_profileDivisionPotentialCoefficient_nonneg
section
noncomputable section
namespace QEC.Locality
private theorem profileDivisionPotential_eq_expanded
    {beta exponent : ℝ} {r parent : Nat} (hr : 0 < r) :
    profileDivisionPotential beta exponent r parent =
      profileDivisionPotentialCoefficient beta exponent *
        ((parent : ℝ) * (r : ℝ) ^ (exponent - 1) /
            (1 / 4 : ℝ) ^ (1 - exponent) -
          (parent : ℝ) ^ exponent) := by
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hrPowPos : 0 < (r : ℝ) ^ exponent := Real.rpow_pos_of_pos hrReal exponent
  rw [profileDivisionPotential, Real.div_rpow (Nat.cast_nonneg parent) hrReal.le,
    Real.rpow_sub_one hrReal.ne']
  field_simp [hrReal.ne', hrPowPos.ne']
end QEC.Locality
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
namespace QEC.Locality
theorem _root_.solution
    {beta exponent : ℝ} {r parent : Nat}
    (hbeta : 0 ≤ beta) (hexponent : 0 < exponent ∧ exponent < 1)
    (hr : 0 < r) :
    profileDivisionPotential beta exponent r parent ≤
      profileDivisionPotentialCoefficient beta exponent *
        ((parent : ℝ) * (r : ℝ) ^ (exponent - 1) /
          (1 / 4 : ℝ) ^ (1 - exponent)) := by
  rw [profileDivisionPotential_eq_expanded hr]
  have hcoefficient := profileDivisionPotentialCoefficient_nonneg hbeta hexponent
  have hparentPower : 0 ≤ (parent : ℝ) ^ exponent :=
    Real.rpow_nonneg (Nat.cast_nonneg parent) exponent
  nlinarith
end QEC.Locality
