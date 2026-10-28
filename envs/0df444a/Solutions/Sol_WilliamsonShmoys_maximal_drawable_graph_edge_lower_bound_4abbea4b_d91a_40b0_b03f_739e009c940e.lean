-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_4abbea4b_d91a_40b0_b03f_739e009c940e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:26:36.177277+00:00
-- url     : https://prove2.me/submissions/b185c1ad-a823-4fdd-a24c-32600c667127
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_triangulation_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hmax : ∀ Q : SimpleGraph V, P ≤ Q →
      WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P) :
    3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by
  obtain ⟨Q, hPQ, hQ, hcard⟩ :=
    WilliamsonShmoys.planar_drawingOn_triangulation_edge_count P hV hP
  have hQP : Q = P := hmax Q hPQ hQ
  have hEq : 3 * Fintype.card V - 6 = P.edgeSet.ncard := by
    simpa only [hQP] using hcard.symm
  exact le_of_eq hEq