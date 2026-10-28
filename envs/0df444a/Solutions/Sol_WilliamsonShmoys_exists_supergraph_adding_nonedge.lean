-- Prove2me | solution 1 for WilliamsonShmoys.exists_supergraph_adding_nonedge
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:42:23.39882+00:00
-- url     : https://prove2.me/submissions/60a8aaab-31b7-4b79-90fe-0bd3065e3d10

import Mathlib

set_option autoImplicit false

theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V) (hNotAdj : ¬ G.Adj u v),
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Adj u v ∧
        ∀ x y, H.Adj x y →
          G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) := by
  intro h
  obtain ⟨H, -, hH, -⟩ := h (⊥ : SimpleGraph Unit) () () (fun h => h)
  exact H.irrefl hH
