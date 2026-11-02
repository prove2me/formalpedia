-- Prove2me | solution 1 for WilliamsonShmoys.planar_add_edge_between_nonreachable_vertices__p2m_71ebc69f_78e1_4174_9ed9_e68a3e8da3bb_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:43:49.410465+00:00
-- url     : https://prove2.me/submissions/b03d13df-7485-422d-86f7-3f67e75242aa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_nonreachable_vertices_geometric_extension__p2m_61c492cb_f898_4cbe_b4f0_23e57d6c2689_a3
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (u v : V)
    (hsep : ¬ N.Reachable u v) (hN : HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V, N ≤ P ∧ P ≠ N ∧ HasPlanarDrawingOn P := by
  obtain ⟨P, hNP, hEdge, hNotEdge, hPlanar⟩ :=
    WilliamsonShmoys.planar_add_edge_between_nonreachable_vertices_geometric_extension__p2m_61c492cb_f898_4cbe_b4f0_23e57d6c2689_a3
      N u v hsep hN
  refine ⟨P, hNP, ?_, hPlanar⟩
  intro hEq
  apply hNotEdge
  rw [hEq] at hEdge
  exact hEdge