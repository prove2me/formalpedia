-- Prove2me | solution 1 for PI.FglChordFactor.Wk.isWq_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:24.157407+00:00
-- url     : https://prove2.me/submissions/8ac1f2e7-9517-426a-8d8f-2ceb5aae9a73

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
theorem _root_.solution {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h : IsWq W wq) : PI.AddIntG.IsWq W wq := h
end PI.FglChordFactor.Wk
