-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:27:19.12792+00:00
-- url     : https://prove2.me/submissions/2b2d66a9-e23f-472c-a78c-1e51c54d3915

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_acyclic_edge_count
import Theorems.Thm_WilliamsonShmoys_planar_drawing_nonacyclic_face_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  by_cases hAcyclic : G.IsAcyclic
  · have hTree :=
      WilliamsonShmoys.connected_acyclic_edge_count G hConnected hAcyclic
    omega
  · obtain ⟨f, hEuler, hSides⟩ :=
      WilliamsonShmoys.planar_drawing_nonacyclic_face_count
        G hConnected hG hAcyclic
    omega