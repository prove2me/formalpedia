-- Prove2me | solution 1 for PI.FglChordFactor.Wk.catC_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:04.661331+00:00
-- url     : https://prove2.me/submissions/a4bcc517-454c-4bb0-90a2-b2ac7ec1dd6f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AddIntG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_NormDeltaWc

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
theorem _root_.solution : catC ^ 2 * PowerSeries.X + 1 = catC := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℂ_[2])) PowerSeries.catalanSeries_sq_mul_X_add_one
  simp only [map_add, map_mul, map_pow, map_one, PowerSeries.map_X] at h
  exact h
end PI.FglChordFactor.Wk
