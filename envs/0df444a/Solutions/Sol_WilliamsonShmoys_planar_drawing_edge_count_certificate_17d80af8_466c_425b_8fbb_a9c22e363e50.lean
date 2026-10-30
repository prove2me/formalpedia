-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_certificate_17d80af8_466c_425b_8fbb_a9c22e363e50
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:09:57.537908+00:00
-- url     : https://prove2.me/submissions/ecea65ca-bcbf-4eec-8f60-30ee344dbed0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count_7c1cdf82
import Theorems.Thm_WilliamsonShmoys_euler_compatible_face_count_incidence_7c1cdf82

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) (hcard : 3 ≤ Fintype.card V) :
    Exists fun f : Nat => Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * H.edgeSet.ncard := by
  exact Exists.elim
    (WilliamsonShmoys.planar_drawing_euler_face_count_7c1cdf82 H hH hconn)
    (fun f heuler => Exists.intro f
      (And.intro heuler
        (WilliamsonShmoys.euler_compatible_face_count_incidence_7c1cdf82
          H hH hconn hcard f heuler)))