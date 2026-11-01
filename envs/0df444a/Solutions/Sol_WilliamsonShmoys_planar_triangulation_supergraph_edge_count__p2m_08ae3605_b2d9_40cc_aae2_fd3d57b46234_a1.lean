-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_edge_count__p2m_08ae3605_b2d9_40cc_aae2_fd3d57b46234_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:48:57.447195+00:00
-- url     : https://prove2.me/submissions/b61ca606-ddf8-4392-a65d-fbd2977c1502
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_49e59269_0942_49a7_bb42_8d7dcf799486_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_49e59269_0942_49a7_bb42_8d7dcf799486_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {U : Type} [Fintype U] [LinearOrder U]
    (H : SimpleGraph U) (hcard : 3 ≤ Fintype.card U)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph U, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card U - 6 = K.edgeSet.ncard := by
  obtain ⟨K, hHK, hdrawK, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_49e59269_0942_49a7_bb42_8d7dcf799486_a1
      H hdraw
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_49e59269_0942_49a7_bb42_8d7dcf799486_a1
      K hcard hdrawK hmax
  exact ⟨K, hHK, hdrawK, hcount⟩