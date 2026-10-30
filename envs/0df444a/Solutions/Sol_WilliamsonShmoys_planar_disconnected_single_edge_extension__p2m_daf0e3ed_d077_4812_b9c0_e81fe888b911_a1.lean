-- Prove2me | solution 1 for WilliamsonShmoys.planar_disconnected_single_edge_extension__p2m_daf0e3ed_d077_4812_b9c0_e81fe888b911_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:40:18.321079+00:00
-- url     : https://prove2.me/submissions/f7cc182e-0871-40ff-98e9-f6ad8f3a99fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_disconnected_has_separated_vertices__p2m_864f1371_5a05_4a46_954d_5d68a77fa253_a1
import Theorems.Thm_WilliamsonShmoys_planar_join_separated_vertices__p2m_864f1371_5a05_4a46_954d_5d68a77fa253_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hdisc : ¬ H.Connected) :
    ∃ G : SimpleGraph V, ∃ u : V, ∃ v : V,
      u ≠ v ∧ ¬ H.Adj u v ∧ H ≤ G ∧ HasPlanarDrawingOn G ∧ G.Adj u v ∧
        ∀ {x y : V}, G.Adj x y →
          H.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  obtain ⟨u, v, huv, hseparate⟩ :=
    WilliamsonShmoys.planar_disconnected_has_separated_vertices__p2m_864f1371_5a05_4a46_954d_5d68a77fa253_a1 H hdisc
  obtain ⟨G, hsub, hdraw, hadj, hnonadj, hexact⟩ :=
    WilliamsonShmoys.planar_join_separated_vertices__p2m_864f1371_5a05_4a46_954d_5d68a77fa253_a1 H hH u v huv hseparate
  exact ⟨G, u, v, huv, hnonadj, hsub, hdraw, hadj, hexact⟩