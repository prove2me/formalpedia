-- Prove2me | solution 1 for QEC.Locality.profileDivisionRegionConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:51:55.257527+00:00
-- url     : https://prove2.me/submissions/0d8db53f-0724-4f36-86e8-781055e2774c

import Definitions.Def_QEC_Locality_SeparatorProfile_DivisionPotential
import Definitions.Def_QEC_Locality_SeparatorProfile_Completion
import Definitions.Def_QEC_Locality_SeparatorProfile_StoppedPotential
import Theorems.Thm_QEC_Locality_markedSpineDecayRatio_lt_one
import Theorems.Thm_QEC_Locality_profileDivisionPotentialCoefficient_pos


set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {beta exponent : ℝ} (hbeta : 1 ≤ beta)
    (hexponent : 0 < exponent ∧ exponent < 1) :
    0 < profileDivisionRegionConstant beta exponent := by
  have hpotential := profileDivisionPotentialCoefficient_pos hbeta hexponent
  have hquarter : 0 < (1 / 4 : ℝ) ^ (1 - exponent) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hdecay : 0 < 1 - markedSpineDecayRatio exponent :=
    sub_pos.mpr (markedSpineDecayRatio_lt_one hexponent.1)
  have hweighted : 0 < beta / (1 - markedSpineDecayRatio exponent) :=
    div_pos (zero_lt_one.trans_le hbeta) hdecay
  unfold profileDivisionRegionConstant profileDivisionChargeRootConstant
    profileDivisionBoundaryRatioConstant
  positivity
end QEC.Locality
