-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.cc_l
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:19.357479+00:00
-- url     : https://prove2.me/submissions/7dff19d4-92cc-4ce3-bac1-d4ad9902051c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
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
private theorem cc_subst_lemma {κ : Type*} {a : MvPowerSeries κ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [map_pow, ha, zero_pow hd]
variable {l ex ph : PowerSeries ℂ_[p]}
variable {s : τ → MvPowerSeries σ ℂ_[p]}
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
namespace PI.UnitaryGroupMassFormula.PhGram
theorem _root_.solution (hD : Data l ex ph) : PowerSeries.constantCoeff l = 0 := by
  have h := cc_subst_lemma (κ := Unit) (a := ex) hD.1 l
  rw [hD.2.1] at h
  exact h.symm.trans PowerSeries.constantCoeff_X
end PI.UnitaryGroupMassFormula.PhGram
