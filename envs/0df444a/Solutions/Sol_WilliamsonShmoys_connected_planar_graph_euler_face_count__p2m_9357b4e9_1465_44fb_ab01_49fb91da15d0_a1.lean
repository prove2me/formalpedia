-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_graph_euler_face_count__p2m_9357b4e9_1465_44fb_ab01_49fb91da15d0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:59:48.737195+00:00
-- url     : https://prove2.me/submissions/475f9ee2-73df-4542-a13c-66d8d95aca3c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_f9c8d92b_3a05_45f0_b41b_64ba71ce8cc1_a5
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_incidence_bound__p2m_f9c8d92b_3a05_45f0_b41b_64ba71ce8cc1_a5

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHconn : ∀ u v, Relation.ReflTransGen H.Adj u v)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * H.edgeSet.ncard := by
  obtain ⟨f, hEuler⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_count__p2m_f9c8d92b_3a05_45f0_b41b_64ba71ce8cc1_a5
      H hHconn hHdraw hV
  exact ⟨f, hEuler,
    WilliamsonShmoys.planar_drawing_face_incidence_bound__p2m_f9c8d92b_3a05_45f0_b41b_64ba71ce8cc1_a5
      H hHconn hHdraw hV f hEuler⟩