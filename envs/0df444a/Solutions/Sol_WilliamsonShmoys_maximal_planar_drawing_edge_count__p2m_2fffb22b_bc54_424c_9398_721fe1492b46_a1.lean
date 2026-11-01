-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_2fffb22b_bc54_424c_9398_721fe1492b46_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:13:22.006572+00:00
-- url     : https://prove2.me/submissions/9f3459fd-e79e-468c-b89b-52aa8a52d86c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_626039db_5057_4194_82d1_e074d68da7fd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_626039db_5057_4194_82d1_e074d68da7fd_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ (G : SimpleGraph V) (dG : DecidableRel G.Adj),
      HasPlanarDrawingOn G →
      (letI : DecidableRel H.Adj := dH
       letI : DecidableRel G.Adj := dG
       H.edgeFinset ⊆ G.edgeFinset → H.edgeFinset = G.edgeFinset))
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel H.Adj := dH
     H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  have hupper :=
    WilliamsonShmoys.planar_edge_count_upper__p2m_626039db_5057_4194_82d1_e074d68da7fd_a1
      H dH hH hcard
  have hlower :=
    WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_626039db_5057_4194_82d1_e074d68da7fd_a1
      H dH hH hmax hcard
  omega