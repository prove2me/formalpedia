-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_a0f5e8a0_e0da_456d_9ce8_2c77e5e78796_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:30:52.08629+00:00
-- url     : https://prove2.me/submissions/d2e916df-15ff-44ad-b318-e833b9548930
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_maximal_completion__p2m_e3eb1401_8114_44d9_870e_95a93988f448_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_e3eb1401_8114_44d9_870e_95a93988f448_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V,
      HasPlanarDrawingOn L ∧
      (∀ u v, G.Adj u v → L.Adj u v) ∧
      (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
       3 * Fintype.card V = L.edgeFinset.card + 6) := by
  obtain ⟨L, hL, hGL, hmax⟩ :=
    WilliamsonShmoys.planar_triangulation_maximal_completion__p2m_e3eb1401_8114_44d9_870e_95a93988f448_a1
      G hV hG
  letI : DecidableRel L.Adj := Classical.decRel L.Adj
  refine ⟨L, hL, hGL, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_e3eb1401_8114_44d9_870e_95a93988f448_a1
    L hV hL hmax