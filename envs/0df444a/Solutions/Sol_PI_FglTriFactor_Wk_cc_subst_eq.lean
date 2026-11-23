-- Prove2me | solution 1 for PI.FglTriFactor.Wk.cc_subst_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:48.902033+00:00
-- url     : https://prove2.me/submissions/3dc09760-bbe7-4216-ae55-801ebf08fce1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglTriFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
import Theorems.Thm_PI_FglTriFactor_Wk_subst_sub
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglTriFactor PI.FglTriFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS)
variable {p : ℕ} [Fact p.Prime]
variable {τ : Type*}
namespace PI.FglTriFactor.Wk
theorem _root_.solution {σ : Type*} {a : σ → MvPowerSeries τ ℂ_[p]} (hA : MvPowerSeries.HasSubst a)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (f : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  have hg : MvPowerSeries.constantCoeff (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) = 0 := by
    rw [map_sub, MvPowerSeries.constantCoeff_C, sub_self]
  have h := MvPowerSeries.constantCoeff_subst_eq_zero hA ha hg
  rw [MvPowerSeries.subst_sub hA, MvPowerSeries.subst_C, map_sub, MvPowerSeries.constantCoeff_C,
    sub_eq_zero] at h
  exact h
end PI.FglTriFactor.Wk
