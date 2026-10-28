-- Prove2me | solution 1 for WilliamsonShmoys.connected_supergraph_of_planar_bridge_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-25T23:25:36.642787+00:00
-- url     : https://prove2.me/submissions/2bc1bb2f-dbf7-45e8-8482-34f834b98a3a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_iterate_bridge_extensions

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (bridge_extension : ∀ (K : SimpleGraph V),
      WilliamsonShmoys.HasPlanarDrawingOn K →
      ¬ (∀ u v : V, Nonempty (K.Walk u v)) →
      ∃ L : SimpleGraph V,
        K ≤ L ∧
        WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∃ u v : V, ¬ Nonempty (K.Walk u v) ∧ L.Adj u v) :
    ∃ H : SimpleGraph V,
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ u v : V, Nonempty (H.Walk u v)) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, hGH, hconn, hH⟩ :=
    WilliamsonShmoys.iterate_bridge_extensions G hG bridge_extension
  exact ⟨H, Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH), hconn, hH⟩