-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_exact_edge_count_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:36:05.786139+00:00
-- url     : https://prove2.me/submissions/12316d98-314f-4cb9-b0f5-3cb009bda626
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_exact_edge_count

set_option autoImplicit false

open WilliamsonShmoys

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K.edgeSet ⊂ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L → False)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  have hExact := WilliamsonShmoys.maximal_drawable_graph_exact_edge_count
    K hK hMax hCard
  omega