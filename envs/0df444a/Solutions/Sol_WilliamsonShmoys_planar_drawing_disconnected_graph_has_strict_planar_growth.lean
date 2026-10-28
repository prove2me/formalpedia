-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_disconnected_graph_has_strict_planar_growth
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:48:34.483783+00:00
-- url     : https://prove2.me/submissions/ea00c5a8-a5e5-4e62-91df-02099368cb4e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_pair_3f511b85_c912_45f3_a8e4_d03a9f62236e
import Theorems.Thm_WilliamsonShmoys_planar_add_separated_pair_3f511b85_c912_45f3_a8e4_d03a9f62236e

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 2 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ G' : SimpleGraph V, G ≤ G' ∧
      WilliamsonShmoys.HasPlanarDrawingOn G' ∧
      G.edgeSet.ncard < G'.edgeSet.ncard := by
  obtain ⟨u, v, huv, hreach⟩ :=
    WilliamsonShmoys.disconnected_pair_3f511b85_c912_45f3_a8e4_d03a9f62236e
      G hV hDisconnected
  exact WilliamsonShmoys.planar_add_separated_pair_3f511b85_c912_45f3_a8e4_d03a9f62236e
    G hG huv hreach