-- Prove2me | solution 1 for PI.FglTriFactor.Wk.sub_pr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:54.196712+00:00
-- url     : https://prove2.me/submissions/02f99b95-85d6-446d-8e7b-5599e621e7e5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglTriFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
import Theorems.Thm_PI_FglTriFactor_Wk_subst_sub
import Theorems.Thm_PI_FglTriFactor_Wk_hasSubst_pr
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
theorem _root_.solution {l ex : PowerSeries ℂ_[p]} (hl : PowerSeries.constantCoeff l = 0)
    {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) :
    sub l ex x y = pr x y (sub l ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) := by
  have hb := hasSubst_pr hx hy
  rw [pr, subst_sub hl hb (MvPowerSeries.constantCoeff_X _) (MvPowerSeries.constantCoeff_X _),
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]
  rfl
end PI.FglTriFactor.Wk
