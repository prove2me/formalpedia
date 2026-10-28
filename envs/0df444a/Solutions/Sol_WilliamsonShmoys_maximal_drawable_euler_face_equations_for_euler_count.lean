-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_euler_face_equations_for_euler_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T11:43:14.958952+00:00
-- url     : https://prove2.me/submissions/fb860732-245f-45c2-9dbf-d2ded7cea355
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_connected_for_euler_equations
import Theorems.Thm_WilliamsonShmoys_connected_drawable_euler_face_count_for_maximal_equations
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_for_euler_equations
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → L = M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  have hConnected : L.Connected :=
    WilliamsonShmoys.maximal_drawable_connected_for_euler_equations
      L hL hMax hCard
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.connected_drawable_euler_face_count_for_maximal_equations
      L hL hConnected
  have hEdges :
      L.edgeSet.ncard + 6 = 3 * Fintype.card V :=
    WilliamsonShmoys.maximal_drawable_edge_count_for_euler_equations
      L hL hMax hCard
  exact ⟨f, hEuler, by omega⟩