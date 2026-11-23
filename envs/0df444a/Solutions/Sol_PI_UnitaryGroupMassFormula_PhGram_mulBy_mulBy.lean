-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.mulBy_mulBy
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:08.689474+00:00
-- url     : https://prove2.me/submissions/1cecc136-e2a9-47f6-a8e1-4f904063536a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_cc_lg
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_lg_pt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhGram
open PI.FglGram
variable {p : ℕ} [Fact p.Prime]
variable {σ τ : Type*}
variable {l ex ph : PowerSeries ℂ_[p]}
namespace PI.UnitaryGroupMassFormula.PhGram
theorem _root_.solution (hD : Data l ex ph) (c d : ℂ_[p]) {a : MvPowerSeries σ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) :
    mulBy l ex d (mulBy l ex c a) = mulBy l ex (d * c) a := by
  show pt ex (MvPowerSeries.C d * lg l (pt ex (MvPowerSeries.C c * lg l a))) =
    pt ex (MvPowerSeries.C (d * c) * lg l a)
  rw [lg_pt hD (by rw [map_mul, cc_lg hD ha, mul_zero]), ← mul_assoc, map_mul]
end PI.UnitaryGroupMassFormula.PhGram
