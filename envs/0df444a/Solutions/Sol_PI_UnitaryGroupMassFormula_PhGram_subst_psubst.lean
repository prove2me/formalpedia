-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.subst_psubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:51.843728+00:00
-- url     : https://prove2.me/submissions/41578b2e-950b-42b1-b317-fefae65e978a

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
private theorem hasSubst_of_constantCoeff_eq_zero_gram_substitution_integral {κ ι : Type*} [Finite ι] {a : ι → MvPowerSeries κ ℂ_[p]}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) : MvPowerSeries.HasSubst a := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by rw [ha i]; exact IsNilpotent.zero)
  | exact ⟨fun i => by rw [ha i]; exact IsNilpotent.zero, by rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩
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
namespace PI.UnitaryGroupMassFormula.PhGram
theorem _root_.solution {s : τ → MvPowerSeries σ ℂ_[p]} (hs : MvPowerSeries.HasSubst s)
    {a : MvPowerSeries τ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst s (PowerSeries.subst a f) = PowerSeries.subst (MvPowerSeries.subst s a) f := by
  have haS : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    hasSubst_of_constantCoeff_eq_zero_gram_substitution_integral (fun _ => ha)
  unfold PowerSeries.subst
  exact MvPowerSeries.subst_comp_subst_apply haS hs f
end PI.UnitaryGroupMassFormula.PhGram
