-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_face_data__p2m_cb41be71_821a_4ee1_8bbc_87748aa8233d_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:08:09.420935+00:00
-- url     : https://prove2.me/submissions/c70af42f-d6e8-4413-b339-5e05b7c5b431
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_dbfda827_a827_4911_8354_de916f36b6c0_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_face_boundary_bound__p2m_dbfda827_a827_4911_8354_de916f36b6c0_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeFinset.card + 2 ∧
      3 * f <= 2 * K.edgeFinset.card := by
  obtain ⟨f, hf⟩ :=
    WilliamsonShmoys.planar_drawing_euler_face_count__p2m_dbfda827_a827_4911_8354_de916f36b6c0_a1
      K dK hconn hK hcard
  refine ⟨f, hf, ?_⟩
  exact WilliamsonShmoys.planar_drawing_face_boundary_bound__p2m_dbfda827_a827_4911_8354_de916f36b6c0_a1
    K dK hconn hK hcard f hf