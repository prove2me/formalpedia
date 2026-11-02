-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_has_unreachable_pair__p2m_0dfd7289_30fc_4048_8084_2297688a9abc_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:42:42.035423+00:00
-- url     : https://prove2.me/submissions/10edc03b-7888-4df8-8643-17bef988af35

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (M : SimpleGraph V), ¬ M.Connected →
          ∃ u v : V, ¬ M.Reachable u v) := by
  intro h
  have hdisc : ¬ (⊥ : SimpleGraph Empty).Connected := by
    intro hc
    rcases hc.nonempty with ⟨x⟩
    exact Empty.elim x
  have hex : ∃ u v : Empty, ¬ (⊥ : SimpleGraph Empty).Reachable u v :=
    @h Empty inferInstance inferInstance (⊥ : SimpleGraph Empty) hdisc
  rcases hex with ⟨u, v, _⟩
  exact Empty.elim u