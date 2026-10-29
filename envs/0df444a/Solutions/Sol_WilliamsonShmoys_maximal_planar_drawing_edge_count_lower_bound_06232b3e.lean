-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_06232b3e
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:15:37.948016+00:00
-- url     : https://prove2.me/submissions/5a4438c8-80b4-47e9-ba05-01ecc767131a

import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion_06232b3e

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, L ≤ K → HasPlanarDrawingOn K → K = L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by
  obtain ⟨K, hLK, hK, hCount⟩ :=
    planar_drawing_has_exact_edge_count_completion_06232b3e L hL hCard
  have hEq : K = L := hmax K hLK hK
  subst K
  exact le_of_eq hCount