-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.subst_phAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:09.048804+00:00
-- url     : https://prove2.me/submissions/ce4888ab-5c3a-4ae8-9490-cd2a8eb41273

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_subst_psubst

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
variable {s : τ → MvPowerSeries σ ℂ_[p]}
namespace PI.UnitaryGroupMassFormula.PhGram
theorem _root_.solution (hs : MvPowerSeries.HasSubst s) {a : MvPowerSeries τ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.subst s (phAt ph a) = phAt ph (MvPowerSeries.subst s a) := subst_psubst hs ha ph
end PI.UnitaryGroupMassFormula.PhGram
