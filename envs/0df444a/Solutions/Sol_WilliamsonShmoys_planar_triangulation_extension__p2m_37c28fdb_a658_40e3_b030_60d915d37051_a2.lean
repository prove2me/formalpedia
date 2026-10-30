-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_37c28fdb_a658_40e3_b030_60d915d37051_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:17:04.644115+00:00
-- url     : https://prove2.me/submissions/ab69d78f-40c2-48f3-8b19-9b37356efd28
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_extension__p2m_04c2f104_e4e1_4da1_bff1_5e666d9628dd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_04c2f104_e4e1_4da1_bff1_5e666d9628dd_a1
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    exists H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H /\
      Set.Subset G.edgeSet H.edgeSet /\
      3 * Fintype.card V <= H.edgeSet.ncard + 6 := by
  obtain ⟨H, hH, hGH, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_planar_extension__p2m_04c2f104_e4e1_4da1_bff1_5e666d9628dd_a1
      G hG
  have hbound :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_04c2f104_e4e1_4da1_bff1_5e666d9628dd_a1
      H hH hmax hV
  exact ⟨H, hH, hGH, hbound⟩
