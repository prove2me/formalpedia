-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6a44195f_ae15_4a06_a6fa_fb89b3d5738f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:46:11.113989+00:00
-- url     : https://prove2.me/submissions/3ddc9bd7-c025-4f28-aa19-c6678d201d9e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_5fb904eb_fef4_45c3_b974_7b95702b51b3_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hmax : forall H : SimpleGraph V, K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hTriangular⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition__p2m_5fb904eb_fef4_45c3_b974_7b95702b51b3_a1
      K hK hmax hV
  omega