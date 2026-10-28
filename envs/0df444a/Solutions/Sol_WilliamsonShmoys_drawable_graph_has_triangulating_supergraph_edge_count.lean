-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_triangulating_supergraph_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T15:59:18.193825+00:00
-- url     : https://prove2.me/submissions/40dc00e3-3274-4405-9568-48fff8dff8dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_finite_drawable_supergraph_maximal
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_euler_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists fun T : SimpleGraph V => K <= T /\
      WilliamsonShmoys.HasPlanarDrawingOn T /\
      T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨T, hKT, hT, hmax⟩ :=
    WilliamsonShmoys.exists_finite_drawable_supergraph_maximal K hK
  have hcount :=
    WilliamsonShmoys.maximal_drawable_graph_euler_count T hV hT hmax
  exact ⟨T, hKT, hT, hcount⟩