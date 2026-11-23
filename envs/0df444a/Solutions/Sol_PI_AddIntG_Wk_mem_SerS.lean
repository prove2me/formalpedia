-- Prove2me | solution 1 for PI.AddIntG.Wk.mem_SerS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:30.803193+00:00
-- url     : https://prove2.me/submissions/a24dedec-7f29-453f-b91b-6c79b885d8d5

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
theorem _root_.solution {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} (f : MvPowerSeries σ K) :
    f ∈ SerS S σ ↔ ∀ e, MvPowerSeries.coeff e f ∈ S := by
  rw [SerS, RingHom.mem_range]
  constructor
  · rintro ⟨g, rfl⟩ e
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff e g).2
  · intro h
    refine ⟨(fun e => ⟨MvPowerSeries.coeff e f, h e⟩ : MvPowerSeries σ S), ?_⟩
    ext e
    rfl
end PI.AddIntG.Wk
