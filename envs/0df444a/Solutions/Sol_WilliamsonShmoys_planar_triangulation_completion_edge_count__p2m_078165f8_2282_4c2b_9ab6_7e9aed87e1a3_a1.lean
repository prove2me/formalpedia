-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion_edge_count__p2m_078165f8_2282_4c2b_9ab6_7e9aed87e1a3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:30:32.007004+00:00
-- url     : https://prove2.me/submissions/f924f439-c910-4499-9866-b3d4cca0b6dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_98c8cf30_bc8e_4089_995f_e52a299a85f1_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_equations__p2m_98c8cf30_bc8e_4089_995f_e52a299a85f1_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hMplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨N, hMN, hNplanar, hNmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_98c8cf30_bc8e_4089_995f_e52a299a85f1_a1
      M hMplanar
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_face_equations__p2m_98c8cf30_bc8e_4089_995f_e52a299a85f1_a1
      N hNplanar hNmax hV
  refine ⟨N, hMN, hNplanar, ?_⟩
  omega