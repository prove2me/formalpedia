-- Prove2me | solution 1 for WilliamsonShmoys.maximal_edge_lower_bound_981f13e1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T06:41:48.160604+00:00
-- url     : https://prove2.me/submissions/77a0835e-b985-461d-b28e-ea931f9dfb6f

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_bound_same_vertices
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, HasPlanarDrawingOn K → G ≤ K → K = G) :
    3 * (Fintype.card V : Int) - 6 <= (G.edgeSet.ncard : Int) := by
  obtain ⟨K, hK, hGK, hBound⟩ :=
    WilliamsonShmoys.planar_drawing_augmentation_bound_same_vertices G hG hCard
  have hEq : K = G := hMax K hK hGK
  subst K
  exact hBound