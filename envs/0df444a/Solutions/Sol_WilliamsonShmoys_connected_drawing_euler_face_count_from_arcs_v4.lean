-- Prove2me | solution 1 for WilliamsonShmoys.connected_drawing_euler_face_count_from_arcs_v4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:45:50.937864+00:00
-- url     : https://prove2.me/submissions/7e652582-3f14-491b-9994-0989c14d1949
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_formula
import Theorems.Thm_WilliamsonShmoys_connected_drawing_simple_planar_edge_bound

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 <= Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f <= 2 * G.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.connected_drawing_euler_formula G hG hConn
  have hEdges :=
    WilliamsonShmoys.connected_drawing_simple_planar_edge_bound G hG hConn hCard
  refine ⟨f, hEuler, ?_⟩
  omega
