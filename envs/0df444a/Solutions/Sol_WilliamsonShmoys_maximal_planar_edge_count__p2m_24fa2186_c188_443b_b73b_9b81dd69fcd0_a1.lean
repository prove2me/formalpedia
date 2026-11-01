-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_24fa2186_c188_443b_b73b_9b81dd69fcd0_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:35:57.042056+00:00
-- url     : https://prove2.me/submissions/72b3e3a2-2cad-4aa0-8c96-24e68beee2ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_edge_count__p2m_08ae3605_b2d9_40cc_aae2_fd3d57b46234_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {U : Type} [Fintype U] [LinearOrder U]
    (H : SimpleGraph U) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph U, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hcard : 3 ≤ Fintype.card U) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card U := by
  classical
  obtain ⟨K, hHK, hKdraw, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_supergraph_edge_count__p2m_08ae3605_b2d9_40cc_aae2_fd3d57b46234_a1
      H hcard hdraw
  have hKH : K = H := hmax K hHK hKdraw
  rw [hKH] at hcount
  omega