-- Prove2me | solution 1 for WilliamsonShmoys.drawable_graph_has_euler_extension_maximal_planar_edge_count__p2m_76f2ce3c_d450_4358_bc4a_f7783646ef08_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:30:52.145062+00:00
-- url     : https://prove2.me/submissions/52727e74-2b94-4ce3-8f20-98732d33c51c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_planar_drawing_edge_upper_bound__p2m_88fa0264_c029_416b_ac57_f33f6676e9cf_a3
import Theorems.Thm_maximal_planar_drawing_edge_lower_bound__p2m_88fa0264_c029_416b_ac57_f33f6676e9cf_a3
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj
     L.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  have hupper :=
    planar_drawing_edge_upper_bound__p2m_88fa0264_c029_416b_ac57_f33f6676e9cf_a3
      L hV hL
  have hlower :=
    maximal_planar_drawing_edge_lower_bound__p2m_88fa0264_c029_416b_ac57_f33f6676e9cf_a3
      L hV hL hmax
  omega