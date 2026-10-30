-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_euler_face_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:19:47.448106+00:00
-- url     : https://prove2.me/submissions/190eace6-bca6-47af-b5a0-14b16f2fd21f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_euler_formula
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ := WilliamsonShmoys.planar_connected_euler_formula
    G hG hconn
  have hEdges := WilliamsonShmoys.planar_simple_edge_bound G hG hV
  refine ⟨f, hEuler, ?_⟩
  nlinarith