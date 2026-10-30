-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_planar_edge_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:21:17.924929+00:00
-- url     : https://prove2.me/submissions/6cc5acee-8ea6-4aeb-aec0-c80d51ae9598

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension_for_maximal_edge_bound_50a3c5c3

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ Q : SimpleGraph V,
      P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P) :
    3 * Fintype.card V ≤ P.edgeSet.ncard + 6 := by
  obtain ⟨Q, hPQ, hQdraw, hQcard⟩ :=
    WilliamsonShmoys.exists_planar_triangulation_extension_for_maximal_edge_bound_50a3c5c3
      P hPdraw hCard
  have hQP : Q = P := hmax Q hPQ hQdraw
  rw [← hQP]
  omega