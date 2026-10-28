-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_triangulation_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:10:27.15712+00:00
-- url     : https://prove2.me/submissions/2ac06337-6526-4b00-b247-ab96dc0cef95
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_triangulation_exists_edge_maximal_planar_supergraph
import Theorems.Thm_WilliamsonShmoys_triangulation_maximal_planar_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      T.edgeSet.ncard ≤ U.edgeSet.ncard ∧
      U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨U, hTU, hU, hmono, hmax⟩ :=
    WilliamsonShmoys.triangulation_exists_edge_maximal_planar_supergraph T hT
  have hcount := WilliamsonShmoys.triangulation_maximal_planar_edge_count U hV hU hmax
  exact ⟨U, hTU, hU, hmono, hcount⟩