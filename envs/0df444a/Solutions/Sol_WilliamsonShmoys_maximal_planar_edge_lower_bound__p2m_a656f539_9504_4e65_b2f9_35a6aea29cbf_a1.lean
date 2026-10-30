-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_a656f539_9504_4e65_b2f9_35a6aea29cbf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T20:19:12.769519+00:00
-- url     : https://prove2.me/submissions/0f4bb540-9196-41bb-b952-a6b863553a37

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exact_edge_count

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      Set.Subset M.edgeSet L.edgeSet) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by
  rcases WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count
      L hV hL with ⟨T, hLT, hT, hcount⟩
  have hLT' : Set.Subset L.edgeSet T.edgeSet := SimpleGraph.edgeSet_mono hLT
  have hTL : Set.Subset T.edgeSet L.edgeSet := hmax T hLT' hT
  have hleLT : L.edgeSet.ncard <= T.edgeSet.ncard := Set.ncard_mono hLT'
  have hleTL : T.edgeSet.ncard <= L.edgeSet.ncard := Set.ncard_mono hTL
  omega