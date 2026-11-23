-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_PhGram_subst_add__9765ee5b53ae
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:51:03.693996+00:00
-- url     : https://prove2.me/submissions/d5384b46-f4f5-4ae4-8812-7946710166d9

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
private theorem subst_add_gram_substitution_integral (hs : MvPowerSeries.HasSubst s) (f g : MvPowerSeries τ ℂ_[p]) :
    MvPowerSeries.subst s (f + g) = MvPowerSeries.subst s f + MvPowerSeries.subst s g := by
  rw [← MvPowerSeries.coe_substAlgHom hs, map_add]
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
    MvPowerSeries.subst s (add l ex a b) = add l ex (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) := by
  have hab : MvPowerSeries.constantCoeff (lg l a + lg l b) = 0 := by
    rw [map_add, cc_lg hD ha, cc_lg hD hb, add_zero]
  show MvPowerSeries.subst s (pt ex (lg l a + lg l b)) =
    pt ex (lg l (MvPowerSeries.subst s a) + lg l (MvPowerSeries.subst s b))
  rw [subst_pt hs hab, subst_add_gram_substitution_integral hs, subst_lg hD hs ha, subst_lg hD hs hb]
end PI.UnitaryGroupMassFormula.PhGram
