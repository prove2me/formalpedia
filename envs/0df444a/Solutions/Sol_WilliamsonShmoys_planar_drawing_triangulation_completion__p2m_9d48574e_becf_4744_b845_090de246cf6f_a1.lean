-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_9d48574e_becf_4744_b845_090de246cf6f_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:28:37.369519+00:00
-- url     : https://prove2.me/submissions/45761c6f-16ca-4e4a-bfa1-68cf21625e00
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_6ab13955_ca33_41a0_b892_672767e48ad0_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_6ab13955_ca33_41a0_b892_672767e48ad0_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn Q) (hV : 3 ≤ Fintype.card V) :
    ∃ R : SimpleGraph V, Q ≤ R ∧ HasPlanarDrawingOn R ∧
      R.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨R, hQR, hDrawR, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_6ab13955_ca33_41a0_b892_672767e48ad0_a1
      Q hDraw
  exact ⟨R, hQR, hDrawR,
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_6ab13955_ca33_41a0_b892_672767e48ad0_a1
      R hDrawR hV hmax⟩