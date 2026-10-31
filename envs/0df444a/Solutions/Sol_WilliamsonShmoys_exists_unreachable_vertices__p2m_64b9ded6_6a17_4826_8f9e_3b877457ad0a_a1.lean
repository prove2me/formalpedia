-- Prove2me | solution 1 for WilliamsonShmoys.exists_unreachable_vertices__p2m_64b9ded6_6a17_4826_8f9e_3b877457ad0a_a1
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T06:15:12.234091+00:00
-- url     : https://prove2.me/submissions/ab87afa4-6133-450d-802e-67c6884cf6b6

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

 theorem solution : ¬ (∀ {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V), ¬ Y.Connected →
      ∃ u v : V, u ≠ v ∧ ¬ Y.Reachable u v) := by
  intro h
  let Y : SimpleGraph Empty := ⊥
  have hnc : ¬ Y.Connected := by
    intro hc
    exact isEmptyElim (Classical.choice (show Nonempty Empty from hc.nonempty))
  obtain ⟨u, v, huv⟩ := h (V := Empty) Y hnc
  exact isEmptyElim u