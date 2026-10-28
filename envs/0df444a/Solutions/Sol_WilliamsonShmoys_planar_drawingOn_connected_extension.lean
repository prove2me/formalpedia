-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_connected_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:35:56.670994+00:00
-- url     : https://prove2.me/submissions/7e5d4fe9-c98a-4647-b421-af588017c24d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_connected_supergraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hV : 3 <= Fintype.card V) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧ Q.Connected ∧
        P.edgeSet.ncard ≤ Q.edgeSet.ncard := by
  obtain ⟨Q, hPQ, hdrawQ, hconn⟩ :=
    WilliamsonShmoys.planar_drawingOn_connected_supergraph P hdraw hV
  refine ⟨Q, hPQ, hdrawQ, hconn, ?_⟩
  exact Set.ncard_mono (SimpleGraph.edgeSet_mono hPQ)