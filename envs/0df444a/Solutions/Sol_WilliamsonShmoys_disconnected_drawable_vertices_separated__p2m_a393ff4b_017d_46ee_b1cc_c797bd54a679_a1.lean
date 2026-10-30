-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_drawable_vertices_separated__p2m_a393ff4b_017d_46ee_b1cc_c797bd54a679_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:29:44.771875+00:00
-- url     : https://prove2.me/submissions/0f796119-109d-474f-bd86-18e451244029

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
        (K : SimpleGraph V), ¬ K.Connected →
        ∃ u v : V, ¬ K.Reachable u v) := by
  intro h
  let K : SimpleGraph Empty := ⊥
  have hdis : ¬ K.Connected := by
    intro hc
    exact isEmptyElim (Classical.choice hc.nonempty)
  obtain ⟨u, v, huv⟩ := h (V := Empty) K hdis
  exact isEmptyElim u