-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_supergraph_three_vertices
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:01:19.035675+00:00
-- url     : https://prove2.me/submissions/f14bb505-c049-43c6-977d-e7bd60abe91e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      Q.Connected ∧
      P ≤ Q ∧
      P.edgeSet.ncard ≤ Q.edgeSet.ncard := by
  obtain ⟨Q, hQ, hConn, hSub⟩ :=
    WilliamsonShmoys.planar_connected_supergraph P hCard hP
  refine ⟨Q, hQ, hConn, hSub, ?_⟩
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hSub)
