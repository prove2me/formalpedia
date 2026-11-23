-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhGram.subst_mulBy
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:51:04.011465+00:00
-- url     : https://prove2.me/submissions/e00acd6f-a927-45d9-b8bc-a8fa2916bde7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_IntegralSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditiveCubes_ConstantCoeffLogEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramSubstitutionIntegral_HasSubstGood
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_cc_lg
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_subst_lg
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhGram_subst_pt
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
private theorem subst_C_mul_gram_substitution_integral (hs : MvPowerSeries.HasSubst s) (c : ℂ_[p])
    (f : MvPowerSeries τ ℂ_[p]) :
    MvPowerSeries.subst s (MvPowerSeries.C c * f) = MvPowerSeries.C c * MvPowerSeries.subst s f := by
  rw [← MvPowerSeries.coe_substAlgHom hs, map_mul]
  congr 1
  exact (MvPowerSeries.substAlgHom hs).commutes c
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
theorem _root_.solution (hD : Data l ex ph) (hs : MvPowerSeries.HasSubst s) (c : ℂ_[p]) {a : MvPowerSeries τ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.subst s (mulBy l ex c a) = mulBy l ex c (MvPowerSeries.subst s a) := by
  show MvPowerSeries.subst s (pt ex (MvPowerSeries.C c * lg l a)) =
    pt ex (MvPowerSeries.C c * lg l (MvPowerSeries.subst s a))
  rw [subst_pt hs (by rw [map_mul, cc_lg hD ha, mul_zero]), subst_C_mul_gram_substitution_integral hs, subst_lg hD hs ha]
end PI.UnitaryGroupMassFormula.PhGram
