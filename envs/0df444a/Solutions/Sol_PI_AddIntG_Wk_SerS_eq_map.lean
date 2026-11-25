-- Prove2me | solution 1 for PI.AddIntG.Wk.SerS_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:50.88629+00:00
-- url     : https://prove2.me/submissions/4cc1206d-7336-46eb-8c5c-41d02f58e15a

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
theorem _root_.solution {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} {f : MvPowerSeries σ K}
    (hf : f ∈ SerS S σ) : ∃ g : MvPowerSeries σ S, MvPowerSeries.map S.subtype g = f :=
  RingHom.mem_range.mp hf
end PI.AddIntG.Wk
