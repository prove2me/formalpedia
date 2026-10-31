-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension__p2m_6fab6ec6_c4a2_4215_b61d_4e14bbc8fe70_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:57:27.701924+00:00
-- url     : https://prove2.me/submissions/fc74f9f4-c200-4f95-9cb6-b488c118d15c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_e017d5db_f58c_45b7_b9c4_b8d059edab95_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_connected__p2m_e017d5db_f58c_45b7_b9c4_b8d059edab95_a2
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    ∃ (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj),
      HasPlanarDrawingOn Q ∧ Q.Connected ∧
        (letI : DecidableRel G.Adj := dG
         letI : DecidableRel Q.Adj := dQ
         G.edgeFinset ⊆ Q.edgeFinset) := by
  classical
  obtain ⟨Q, dQ, hQ, hsub, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_e017d5db_f58c_45b7_b9c4_b8d059edab95_a2
      G dG hG
  refine ⟨Q, dQ, hQ, ?_, hsub⟩
  exact WilliamsonShmoys.maximal_planar_graph_connected__p2m_e017d5db_f58c_45b7_b9c4_b8d059edab95_a2
    Q dQ (by omega) hQ hmax