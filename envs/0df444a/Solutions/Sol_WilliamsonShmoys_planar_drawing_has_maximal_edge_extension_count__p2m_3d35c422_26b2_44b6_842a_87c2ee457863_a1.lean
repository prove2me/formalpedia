-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_has_maximal_edge_extension_count__p2m_3d35c422_26b2_44b6_842a_87c2ee457863_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:24:37.387911+00:00
-- url     : https://prove2.me/submissions/b24d88ee-6da7-448a-b1df-130ce6cfc358
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_supergraph__p2m_2b94d345_c453_470c_8517_8648e22306c1_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_2b94d345_c453_470c_8517_8648e22306c1_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, H ≤ L ∧ HasPlanarDrawingOn L ∧
      3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  obtain ⟨L, hHL, hDrawL, hMax⟩ := drawable_graph_has_maximal_supergraph__p2m_2b94d345_c453_470c_8517_8648e22306c1_a1 H hH
  exact ⟨L, hHL, hDrawL,
    maximal_drawable_graph_edge_count__p2m_2b94d345_c453_470c_8517_8648e22306c1_a1 L hDrawL hV hMax⟩