-- Prove2me | solution 1 for PI.FglChordFactor.Wk.wqc_isWq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:46:31.963947+00:00
-- url     : https://prove2.me/submissions/bcfaec35-64e9-4b4f-bbfc-3da24899c56e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AddIntG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_NormDeltaWc
import Theorems.Thm_PI_FglChordFactor_Wk_catC_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.FglChordFactor PI.FglChordFactor.Wk
namespace PI.FglChordFactor.Wk
theorem _root_.solution : IsWq Wc wqc := by
  have hX3 : PowerSeries.HasSubst (PowerSeries.X ^ 3 : PowerSeries ℂ_[2]) :=
    PowerSeries.HasSubst.X_pow (by norm_num)
  have h1 : PowerSeries.subst (PowerSeries.X ^ 3 : PowerSeries ℂ_[2]) (1 : PowerSeries ℂ_[2]) = 1 := by
    rw [← PowerSeries.coe_substAlgHom hX3, map_one]
  have key := congrArg (PowerSeries.subst (PowerSeries.X ^ 3 : PowerSeries ℂ_[2])) catC_eq
  rw [PowerSeries.subst_add hX3, PowerSeries.subst_mul hX3, PowerSeries.subst_pow hX3,
    PowerSeries.subst_X hX3, h1] at key
  simp only [IsWq, Wc, map_zero, map_one, zero_mul, add_zero, one_mul]
  rw [wqc]
  linear_combination -key
end PI.FglChordFactor.Wk
