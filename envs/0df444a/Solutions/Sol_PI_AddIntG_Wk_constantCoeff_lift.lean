-- Prove2me | solution 1 for PI.AddIntG.Wk.constantCoeff_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:01:35.530408+00:00
-- url     : https://prove2.me/submissions/13b5078f-e116-421a-8f2e-5507c311180e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AddIntG PI.AddIntG.Wk
namespace PI.AddIntG.Wk
theorem _root_.solution {K : Type*} [CommRing K] (S : Subring K) {σ : Type*}
    (g : MvPowerSeries σ S) {c : S} (h : MvPowerSeries.constantCoeff (MvPowerSeries.map S.subtype g) = (c : K)) :
    MvPowerSeries.constantCoeff g = c := by
  apply Subtype.ext
  rw [← h]
  simp
end PI.AddIntG.Wk
