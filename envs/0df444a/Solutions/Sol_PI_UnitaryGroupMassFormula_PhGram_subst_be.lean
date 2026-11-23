-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.subst_be
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:54:17.154591+00:00
-- url     : https://prove2.me/submissions/53174f09-669e-4801-91db-0530994d3526

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_cc_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_subst_phAt
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_PhGram_subst_add__9765ee5b53ae
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Classical
namespace PI.UnitaryGroupMassFormula.PhGram
open PI.FglGram
variable {p : ℕ} [Fact p.Prime]
section Exact
variable {σ τ : Type*}
variable {l ex ph : PowerSeries ℂ_[p]}
variable {s : τ → MvPowerSeries σ ℂ_[p]}
private theorem subst_sub_gram_substitution_integral (hs : MvPowerSeries.HasSubst s) (f g : MvPowerSeries τ ℂ_[p]) :
    MvPowerSeries.subst s (f - g) = MvPowerSeries.subst s f - MvPowerSeries.subst s g := by
  rw [← MvPowerSeries.coe_substAlgHom hs, map_sub]
end Exact
end PI.UnitaryGroupMassFormula.PhGram
end
end

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
theorem _root_.solution (hD : Data l ex ph) (hs : MvPowerSeries.HasSubst s) {a b : MvPowerSeries τ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst s (be l ex ph a b) = be l ex ph (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) := by
  show MvPowerSeries.subst s (phAt ph (add l ex a b) - phAt ph a - phAt ph b) =
    phAt ph (add l ex (MvPowerSeries.subst s a) (MvPowerSeries.subst s b)) -
      phAt ph (MvPowerSeries.subst s a) - phAt ph (MvPowerSeries.subst s b)
  rw [subst_sub_gram_substitution_integral hs, subst_sub_gram_substitution_integral hs, subst_phAt hs (cc_add hD ha hb), subst_phAt hs ha,
    subst_phAt hs hb, subst_add' hD hs ha hb]
end PI.UnitaryGroupMassFormula.PhGram
