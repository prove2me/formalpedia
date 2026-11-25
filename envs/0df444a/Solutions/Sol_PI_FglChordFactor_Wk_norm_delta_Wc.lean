-- Prove2me | solution 1 for PI.FglChordFactor.Wk.norm_delta_Wc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:39:11.8666+00:00
-- url     : https://prove2.me/submissions/88a8b7a8-28bf-4882-88dc-b40ec945f4f4

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
theorem _root_.solution : ‖Wc.Δ‖ = 1 := by
  have hΔ : Wc.Δ = -27 := by
    simp only [Wc, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    norm_num
  have h27 : ‖(27 : ℚ_[2])‖ = 1 := by
    have := (Padic.norm_natCast_eq_one_iff (p := 2) (n := 27)).2 (by norm_num)
    simpa using this
  have hc : (27 : ℂ_[2]) = algebraMap ℚ_[2] ℂ_[2] 27 := (map_ofNat _ 27).symm
  rw [hΔ, norm_neg, hc, norm_algebraMap', h27]
end PI.FglChordFactor.Wk
