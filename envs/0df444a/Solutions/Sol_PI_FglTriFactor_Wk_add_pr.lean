-- Prove2me | solution 1 for PI.FglTriFactor.Wk.add_pr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:49.145462+00:00
-- url     : https://prove2.me/submissions/f662f7a3-31a7-4b07-a610-055b3d521c75

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglTriFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CoeffSubstUpdZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
import Theorems.Thm_PI_FglTriFactor_Wk_subst_add
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
    add l ex x y = pr x y (add l ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) := by
  have hb := hasSubst_pr hx hy
  rw [pr, subst_add hl hb (MvPowerSeries.constantCoeff_X _) (MvPowerSeries.constantCoeff_X _),
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]
  rfl
end PI.FglTriFactor.Wk
