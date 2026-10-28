-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_count_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:17:42.719544+00:00
-- url     : https://prove2.me/submissions/45173693-a1b1-41ff-9781-350a22d6b89e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_bound
import Theorems.Thm_WilliamsonShmoys_connected_graph_edge_count_lower_bound

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by
  have hLower : Fintype.card V ≤ G.edgeSet.ncard + 1 :=
    WilliamsonShmoys.connected_graph_edge_count_lower_bound G hConnected
  have hUpper : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.planar_drawing_edge_count_bound G hV hConnected hG
  refine ⟨G.edgeSet.ncard + 2 - Fintype.card V, ?_, ?_⟩
  · omega
  · omega