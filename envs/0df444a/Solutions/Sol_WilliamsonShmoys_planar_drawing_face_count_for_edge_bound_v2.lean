-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_count_for_edge_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:27:12.745079+00:00
-- url     : https://prove2.me/submissions/1e8e0a1f-0c7d-4f90-b783-e5c05f5c228a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count_v2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_incidence_bound_v2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hConnected : L.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * L.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_count_v2
      L hLdraw hConnected
  exact ⟨f, hEuler,
    WilliamsonShmoys.planar_drawing_incidence_bound_v2
      L hLdraw hConnected hCard f hEuler⟩