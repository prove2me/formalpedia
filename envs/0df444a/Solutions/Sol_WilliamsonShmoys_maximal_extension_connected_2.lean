-- Prove2me | solution 2 for WilliamsonShmoys.maximal_extension_connected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:32:08.730383+00:00
-- url     : https://prove2.me/submissions/8552fdab-9655-47df-8816-29d93fc9f964

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P H)
    (hmax : ∀ J : SimpleGraph V, H ≤ J → P J → J = H)
    (bridge_extension : ∀ (J : SimpleGraph V),
      P J →
      ¬ (∀ u v : V, Nonempty (J.Walk u v)) →
      ∃ L : SimpleGraph V,
        J ≤ L ∧ P L ∧
        ∃ u v : V, ¬ Nonempty (J.Walk u v) ∧ L.Adj u v) :
    ∀ u v : V, Nonempty (H.Walk u v) := by
  by_contra hc
  obtain ⟨L, hL, hPL, u, v, huv, hadj⟩ := bridge_extension H hP hc
  have := hmax L hL hPL
  subst this
  exact huv ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil⟩
