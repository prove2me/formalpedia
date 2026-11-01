-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_face_count__p2m_edf71842_1b5c_4584_b66a_8a3d7af33e5d_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:00:18.662725+00:00
-- url     : https://prove2.me/submissions/a37a1f63-504d-4d62-9e01-a4579275021d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_connected__p2m_6a6f73b1_aafd_4ec3_b910_d68356c6d6db_a1
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler__p2m_6a6f73b1_aafd_4ec3_b910_d68356c6d6db_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound__p2m_6a6f73b1_aafd_4ec3_b910_d68356c6d6db_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = G)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel _
     ∃ f : ℕ,
       Fintype.card V + f = G.edgeFinset.card + 2 ∧
       3 * f ≤ 2 * G.edgeFinset.card) := by
  letI : DecidableRel G.Adj := Classical.decRel _
  have hconn :=
    WilliamsonShmoys.maximal_planar_drawing_connected__p2m_6a6f73b1_aafd_4ec3_b910_d68356c6d6db_a1
      G hG hmax hcard
  obtain ⟨f, heuler⟩ :=
    WilliamsonShmoys.connected_planar_drawing_euler__p2m_6a6f73b1_aafd_4ec3_b910_d68356c6d6db_a1
      G hG hconn
  have hedge :=
    WilliamsonShmoys.maximal_planar_drawing_edge_bound__p2m_6a6f73b1_aafd_4ec3_b910_d68356c6d6db_a1
      G hG hmax hcard
  refine ⟨f, heuler, ?_⟩
  nlinarith
