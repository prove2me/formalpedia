-- Prove2me | solution 1 for PI.FglTriFactor.Wk.hasSubst_zc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:05.635232+00:00
-- url     : https://prove2.me/submissions/94e8ce55-66e5-429c-983b-22fa4c6f551c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_SubstUpdateVarTwoLiftedThirdRoot
import Theorems.Thm_PI_FglTriFactor_Wk_zc_const
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
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglTriFactor.Wk
theorem _root_.solution : MvPowerSeries.HasSubst (zc (p := p)) := by
  first
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun i => zc_const i)
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun i => zc_const (p := p) i)
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => zc_const i)
  | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by rw [zc_const i]; exact IsNilpotent.zero)
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (a := zc (p := p)) (by intro i; exact zc_const i)
end PI.FglTriFactor.Wk
