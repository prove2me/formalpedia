-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_euler_face_counts__p2m_22003a04_aff0_4d5b_b1d3_902c88d5c97f_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:52:02.497496+00:00
-- url     : https://prove2.me/submissions/65a3d57d-6314-48bb-8f95-0cfcfcb49c2f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_equation_from_planar_drawing__p2m_2fa1cccf_2cb6_486c_a6c5_c4c514b22b8e_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_incidence_bound__p2m_2fa1cccf_2cb6_486c_a6c5_c4c514b22b8e_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ edgeCount faceCount : ℕ,
      G.edgeSet.ncard = edgeCount ∧
      Fintype.card V + faceCount = edgeCount + 2 ∧
      3 * faceCount <= 2 * edgeCount := by
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_equation_from_planar_drawing__p2m_2fa1cccf_2cb6_486c_a6c5_c4c514b22b8e_a2
      G hcard hconn hG
  have hinc :=
    WilliamsonShmoys.planar_drawing_face_incidence_bound__p2m_2fa1cccf_2cb6_486c_a6c5_c4c514b22b8e_a2
      G hcard hconn hG f heuler
  exact ⟨G.edgeSet.ncard, f, rfl, by omega, by omega⟩