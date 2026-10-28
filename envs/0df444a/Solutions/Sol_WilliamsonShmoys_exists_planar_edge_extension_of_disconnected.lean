-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_edge_extension_of_disconnected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:24:13.846645+00:00
-- url     : https://prove2.me/submissions/e84af1b7-3ad2-4a2b-b683-ab4fbed725a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_nonreachable_pair_of_not_connected
import Theorems.Thm_WilliamsonShmoys_exists_planar_edge_extension_for_pair

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∃ u v : V, ¬ G.Reachable u v ∧ K.Adj u v := by
  obtain ⟨u, v, huv⟩ :=
    WilliamsonShmoys.exists_nonreachable_pair_of_not_connected G hCard hDisconnected
  obtain ⟨K, hGK, hK, huvK⟩ :=
    WilliamsonShmoys.exists_planar_edge_extension_for_pair G hG u v huv
  exact ⟨K, hGK, hK, u, v, huv, huvK⟩