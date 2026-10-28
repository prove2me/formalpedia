-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:28:37.13544+00:00
-- url     : https://prove2.me/submissions/4dfe61cb-35f2-4720-ad6b-7cc3c68cee8d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Theorems.Thm_WilliamsonShmoys_connected_planar_supergraph_geometry
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      (∀ u v, L.Adj u v → H.Adj u v) ∧
      H.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      L.edgeSet.ncard ≤ H.edgeSet.ncard := by
  obtain ⟨H, hsub, hconn, hplan⟩ :=
    WilliamsonShmoys.connected_planar_supergraph_geometry L hV hL
  refine ⟨H, hsub, hconn, hplan, ?_⟩
  exact WilliamsonShmoys.edgeSet_ncard_mono L H hsub