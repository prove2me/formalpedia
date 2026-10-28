-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_on_fixed_vertex_type_4156f0d3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:08:29.765526+00:00
-- url     : https://prove2.me/submissions/4c8aaf0a-6391-4c88-adca-ab220bd52d41
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal_aea3a4e2
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_aea3a4e2

open WilliamsonShmoys

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : forall K : SimpleGraph V, Set.Subset H.edgeSet K.edgeSet ->
      HasPlanarDrawingOn K -> Set.Subset K.edgeSet H.edgeSet) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hKmax⟩ :=
    WilliamsonShmoys.drawable_supergraph_maximal_aea3a4e2 H hH
  have hKH := hmax K hHK hK
  have hKcount :=
    WilliamsonShmoys.maximal_drawable_graph_edge_count_aea3a4e2 K hV hK hKmax
  have hsets : H.edgeSet = K.edgeSet := Set.Subset.antisymm hHK hKH
  rw [hsets]
  exact hKcount