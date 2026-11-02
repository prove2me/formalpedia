-- Prove2me | solution 1 for WilliamsonShmoys.triangulate_connected_planar_drawing__p2m_182810d1_e6dd_4dca_a527_6379c248c599_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:36:16.092502+00:00
-- url     : https://prove2.me/submissions/d2bba694-0713-4d15-932d-cff116b3c38a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_f3a63840_9387_418b_904c_fbe2e8408361_a1
import Theorems.Thm_WilliamsonShmoys_graph_edge_completion__p2m_f3a63840_9387_418b_904c_fbe2e8408361_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_capacity__p2m_f3a63840_9387_418b_904c_fbe2e8408361_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hconnected : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    letI : (G : SimpleGraph V) → DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    ∃ H : SimpleGraph V, K ≤ H ∧
      H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  classical
  let n := Fintype.card V
  have hplanar :=
    WilliamsonShmoys.planar_drawing_edge_bound__p2m_f3a63840_9387_418b_904c_fbe2e8408361_a1
      K hcard hconnected hdraw
  have hcapacity :=
    WilliamsonShmoys.planar_edge_count_capacity__p2m_f3a63840_9387_418b_904c_fbe2e8408361_a1
      n hcard
  exact WilliamsonShmoys.graph_edge_completion__p2m_f3a63840_9387_418b_904c_fbe2e8408361_a1
    K (3 * n - 6) hplanar hcapacity