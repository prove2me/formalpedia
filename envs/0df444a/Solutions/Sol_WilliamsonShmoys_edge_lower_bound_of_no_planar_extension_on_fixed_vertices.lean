-- Prove2me | solution 1 for WilliamsonShmoys.edge_lower_bound_of_no_planar_extension_on_fixed_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:28:20.094972+00:00
-- url     : https://prove2.me/submissions/6aa8658f-d07d-4751-a330-8e52d7dc1ce5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_fd5841b3_47d6_4110_a690_9c63bff57c51

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (hV : 3 <= Fintype.card V)
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hmax : ∀ Q : SimpleGraph V, P ≤ Q →
      WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P) :
    3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by
  obtain ⟨Q, hPQ, hQ, hEdges⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_fd5841b3_47d6_4110_a690_9c63bff57c51 hV P hP
  have hEq : Q = P := hmax Q hPQ hQ
  rw [hEq] at hEdges
  exact Nat.le_of_eq hEdges