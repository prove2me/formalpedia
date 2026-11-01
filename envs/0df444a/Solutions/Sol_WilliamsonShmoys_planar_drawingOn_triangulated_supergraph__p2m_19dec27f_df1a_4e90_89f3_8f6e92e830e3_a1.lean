-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_triangulated_supergraph__p2m_19dec27f_df1a_4e90_89f3_8f6e92e830e3_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:18:16.920203+00:00
-- url     : https://prove2.me/submissions/79224e8d-da7d-415d-87f6-9698f322fe8e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_ac4b6b7c_6a36_45ce_9f61_962873444f22_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ac4b6b7c_6a36_45ce_9f61_962873444f22_a2
import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension__p2m_ac4b6b7c_6a36_45ce_9f61_962873444f22_a2
      G hG hV
  exact ⟨H, hGH, hH,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_ac4b6b7c_6a36_45ce_9f61_962873444f22_a2
      H hH hV hmax⟩