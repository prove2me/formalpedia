-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_simple_edge_bound__p2m_3948e52b_b0d7_479f_b947_2a84e2ebda9e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:08:06.597069+00:00
-- url     : https://prove2.me/submissions/07e0af9f-68af-4a7c-aa4a-c5d22dd71c66
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_maximal_extension__p2m_2a90ede6_b2ad_40d4_a25e_8e3e873838ed_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_2a90ede6_b2ad_40d4_a25e_8e3e873838ed_a1
import Theorems.Thm_WilliamsonShmoys_simpleGraph_edgeSet_ncard_mono__p2m_2a90ede6_b2ad_40d4_a25e_8e3e873838ed_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hHconn : ∀ u v, Relation.ReflTransGen H.Adj u v)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKdraw, hKconn, hKmax⟩ :=
    WilliamsonShmoys.connected_planar_drawing_maximal_extension__p2m_2a90ede6_b2ad_40d4_a25e_8e3e873838ed_a1
      H hHconn hHdraw hV
  have hKcount :=
    WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_2a90ede6_b2ad_40d4_a25e_8e3e873838ed_a1
      K hKdraw hKconn hKmax hV
  have hmono :=
    WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono__p2m_2a90ede6_b2ad_40d4_a25e_8e3e873838ed_a1
      H K hHK
  omega