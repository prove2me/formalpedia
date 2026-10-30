-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation_for_edge_bound_5164bdb5_maximal_planar_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:12:02.483005+00:00
-- url     : https://prove2.me/submissions/4872ab83-55e6-4038-926c-f2c53a9a39f0

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_edge_count

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hLM, hM, hCount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_edge_count L hV hL
  have hML : M = L := hMax M hLM hM
  simpa [hML] using hCount