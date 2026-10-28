-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_count_equations
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:16:59.209653+00:00
-- url     : https://prove2.me/submissions/4fe84dd4-ee96-461e-845f-ebc7c209c241
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_euler_face_count
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_incidence_for_euler_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → L = M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.maximal_drawable_graph_euler_face_count L hL hMax hCard
  exact ⟨f, hEuler,
    WilliamsonShmoys.maximal_drawable_graph_incidence_for_euler_count
      L hL hMax hCard f hEuler⟩