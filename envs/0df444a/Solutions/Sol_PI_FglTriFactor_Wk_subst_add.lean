-- Prove2me | solution 1 for PI.FglTriFactor.Wk.subst_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:15.279571+00:00
-- url     : https://prove2.me/submissions/c5e454da-4130-49be-9930-0e7571710c3d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglTriFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
import Theorems.Thm_PI_FglTriFactor_Wk_cc_lg
import Theorems.Thm_PI_FglTriFactor_Wk_subst_lg
import Theorems.Thm_PI_FglTriFactor_Wk_subst_pt
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
variable {l ex : PowerSeries ℂ_[p]} {σ τ : Type*}
namespace PI.FglTriFactor.Wk
theorem _root_.solution (hl : PowerSeries.constantCoeff l = 0) {b : σ → MvPowerSeries τ ℂ_[p]}
    (hb : MvPowerSeries.HasSubst b) {x y : MvPowerSeries σ ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.subst b (add l ex x y) = add l ex (MvPowerSeries.subst b x) (MvPowerSeries.subst b y) := by
  have h0 : MvPowerSeries.constantCoeff (PI.FglTriFactor.lg l x + PI.FglTriFactor.lg l y) = 0 := by
    rw [map_add, cc_lg hl hx, cc_lg hl hy, add_zero]
  unfold PI.FglTriFactor.add
  rw [subst_pt hb h0, MvPowerSeries.subst_add hb, subst_lg hb hx, subst_lg hb hy]
end PI.FglTriFactor.Wk
