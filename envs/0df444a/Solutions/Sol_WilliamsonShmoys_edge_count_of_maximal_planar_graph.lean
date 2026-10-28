-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_of_maximal_planar_graph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T09:17:09.809193+00:00
-- url     : https://prove2.me/submissions/6f8671ca-e233-48a2-b268-00b164f799a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_lower_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hUpper := WilliamsonShmoys.planar_drawingOn_edge_upper_bound K hV hK
  have hLower := WilliamsonShmoys.maximal_planar_drawingOn_edge_lower_bound K hV hK hMax
  omega