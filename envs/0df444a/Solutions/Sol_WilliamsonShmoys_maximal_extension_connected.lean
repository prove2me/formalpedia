-- Prove2me | solution 1 for WilliamsonShmoys.maximal_extension_connected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:32:05.451217+00:00
-- url     : https://prove2.me/submissions/7ca86904-4b74-41d3-b7fc-2de851237454

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
  classical
  by_contra hc
  obtain ⟨L, hHL, hPL, u, v, huv, hL⟩ := bridge_extension H hP hc
  rw [hmax L hHL hPL] at hL
  exact huv ⟨hL.toWalk⟩
